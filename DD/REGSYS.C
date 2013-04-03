//======================================================================
// 
// Regsys.c
//
// Copyright (C) 1996-1998 Mark Russinovich and Bryce Cogswell
//
// Hooks the registry by replacing registry related calls in the system
// service table with pointers to our own hook routines. Very simple
// yet very effective.
//
//======================================================================
#include "ntddk.h"
#include "stdarg.h"
#include "stdio.h"
#include "..\gui\ioctlcmd.h"
#include "regsys.h"

//----------------------------------------------------------------------
//                           DEFINES
//----------------------------------------------------------------------
// print macro that only turns on when debugging is on
#if DBG
#define DbgPrint(arg) DbgPrint arg
#else
#define DbgPrint(arg) 
#endif

//
// Macro for easy hook/unhook. On X86 implementations of Zw* functions, the DWORD
// following the first byte is the system call number, so we reach into the Zw function
// passed as a parameter, and pull the number out. This makes system call hooking
// dependent ONLY on the Zw* function implementation not changing.
//

#if defined(_ALPHA_)
#define SYSCALL(_function)  ServiceTable->ServiceTable[ (*(PULONG)_function)  & 0x0000FFFF ]
#else
#define SYSCALL(_function)  ServiceTable->ServiceTable[ *(PULONG)((PUCHAR)_function+1)]
#endif

//
// Number of predefined rootkeys
//
#define NUMROOTKEYS     4


//
// The name of the System process, in which context we're called in our DriverEntry
//
#define SYSNAME         "System"

//
// A unicode string constant for the "default" value
//
#define DEFAULTNAMELEN  (9*sizeof(WCHAR))
WCHAR                   DefaultValueString[] = L"(Default)";
UNICODE_STRING          DefaultValue = {
    DEFAULTNAMELEN,
    DEFAULTNAMELEN,
    DefaultValueString
};

//
// A filter to use if we're monitoring boot activity
//
FILTER  BootFilter = {
    "*", "", "*", "",
    TRUE, TRUE, TRUE, TRUE 
};

//----------------------------------------------------------------------
//                         FORWARD DEFINES
//---------------------------------------------------------------------- 
NTSTATUS RegmonDispatch( IN PDEVICE_OBJECT DeviceObject, IN PIRP Irp );
VOID     RegmonUnload( IN PDRIVER_OBJECT DriverObject );

//----------------------------------------------------------------------
//                         GLOBALS
//---------------------------------------------------------------------- 
// our user-inteface device object
PDEVICE_OBJECT          GUIDevice;

//
// Is a GUI talking to us?
//
BOOLEAN                 GUIActive = FALSE;

//
// Are we logging a boot sequence?
//
BOOLEAN                 BootLogging = FALSE;
KEVENT                  LoggingEvent;
HANDLE                  LogFile = INVALID_HANDLE_VALUE;
PSTORE_BUF              BootSavedStoreList = NULL;
PSTORE_BUF              BootSavedStoreTail;

//
// Is registry hooked?
//
BOOLEAN                 RegHooked = FALSE;

//
// Global error string
//
CHAR                    errstring[256];

//
// Global filter (sent to us by the GUI)
//
FILTER                  FilterDef;

//
// Lock to protect filter arrays
//
KMUTEX                  FilterMutex;

//
// Array of process and path filters 
//
ULONG                   NumProcessFilters = 0;
PCHAR                   ProcessFilters[MAXFILTERS];
ULONG                   NumProcessExcludeFilters = 0;
PCHAR                   ProcessExcludeFilters[MAXFILTERS];
ULONG                   NumPathIncludeFilters = 0;
PCHAR                   PathIncludeFilters[MAXFILTERS];
ULONG                   NumPathExcludeFilters = 0;
PCHAR                   PathExcludeFilters[MAXFILTERS];

//
// Pointer to system global service table
//
PSRVTABLE               ServiceTable;

//
// This is the offset into a KPEB of the current process name. This is determined
// dynamically by scanning the process block belonging to the GUI for its name.
//
ULONG                   ProcessNameOffset;

//
// We save off pointers to the actual Registry functions in these variables
//
NTSTATUS (*RealRegOpenKey)( IN PHANDLE, IN OUT ACCESS_MASK, IN POBJECT_ATTRIBUTES );
NTSTATUS (*RealRegQueryKey)( IN HANDLE, IN KEY_INFORMATION_CLASS,
                             OUT PVOID, IN ULONG, OUT PULONG );
NTSTATUS (*RealRegQueryValueKey)( IN HANDLE, IN PUNICODE_STRING, 
                                  IN KEY_VALUE_INFORMATION_CLASS,
                                  OUT PVOID, IN ULONG, OUT PULONG );
NTSTATUS (*RealRegEnumerateValueKey)( IN HANDLE, IN ULONG,  
                                      IN KEY_VALUE_INFORMATION_CLASS,
                                      OUT PVOID, IN ULONG, OUT PULONG );
NTSTATUS (*RealRegEnumerateKey)( IN HANDLE, IN ULONG,
                                 IN KEY_INFORMATION_CLASS,
                                 OUT PVOID, IN ULONG, OUT PULONG );
NTSTATUS (*RealRegSetValueKey)( IN HANDLE KeyHandle, IN PUNICODE_STRING ValueName,
                                IN ULONG TitleIndex, IN ULONG Type, 
                                IN PVOID Data, IN ULONG DataSize );
NTSTATUS (*RealRegCreateKey)( OUT PHANDLE, IN ACCESS_MASK,
                              IN POBJECT_ATTRIBUTES , IN ULONG,
                              IN PUNICODE_STRING, IN ULONG, OUT PULONG );
NTSTATUS (*RealRegDeleteValueKey)( IN HANDLE, IN PUNICODE_STRING );
NTSTATUS (*RealRegCloseKey)( IN HANDLE );
NTSTATUS (*RealRegDeleteKey)( IN HANDLE );
NTSTATUS (*RealRegFlushKey)( IN HANDLE );

//
// Lenghs of rootkeys (filled in at init). This table allows us to translate 
// path names into better-known forms. Current user is treated specially since
// its not a full match.
//
ROOTKEY CurrentUser[2] = {
    { "\\\\REGISTRY\\USER\\S", "HKCU", 0 },
    { "HKU\\S", "HKCU", 0 }
};

ROOTKEY RootKey[NUMROOTKEYS] = {
    { "\\\\REGISTRY\\USER", "HKU", 0 },
    { "\\\\REGISTRY\\MACHINE\\SYSTEM\\CURRENTCONTROLSET\\HARDWARE PROFILES\\CURRENT", 
      "HKCC", 0 },
    { "\\\\REGISTRY\\MACHINE\\SOFTWARE\\CLASSES", "HKCR", 0 },
    { "\\\\REGISTRY\\MACHINE", "HKLM", 0 }
};

//
// This is a hash table for keeping names around for quick lookup.
//
PHASH_ENTRY             HashTable[NUMHASH];

//
// Mutex for hash table accesses
//
KMUTEX                  HashMutex;

//
// Data structure for storing messages we generate
//
PSTORE_BUF              Store           = NULL;
ULONG                   Sequence        = 0;
KMUTEX                  StoreMutex;

//
// Maximum amount of data we will grab for buffered unread data
//
ULONG                   NumStore        = 0;
ULONG                   MaxStore        = MAXMEM/MAX_STORE;

//
// Free hash list. Note: we don't use lookaside lists since
// we want to be able to run on NT 3.51 - lookasides were
// introduced in NT 4.0
//
PHASH_ENTRY             FreeHashList = NULL;


//======================================================================
//      P A T T E R N   M A T C H I N G   R O U T I N E S
//======================================================================


//----------------------------------------------------------------------
//
// MatchOkay
//
// Only thing left after compare is more mask. This routine makes
// sure that its a valid wild card ending so that its really a match.
//
//----------------------------------------------------------------------
BOOLEAN MatchOkay( PCHAR Pattern )
{
    //
    // If pattern isn't empty, it must be a wildcard
    //
    if( *Pattern && *Pattern != '*' ) {
 
        return FALSE;
    }

    //
    // Matched
    //
    return TRUE;
}



//----------------------------------------------------------------------
//
// MatchWithPattern
//
// Performs nifty wildcard comparison.
//
//----------------------------------------------------------------------
BOOLEAN MatchWithPattern( PCHAR Pattern, PCHAR Name )
{
    CHAR   upcase;

    //
    // End of pattern?
    //
    if( !*Pattern ) {

        return FALSE;
    }

    //
    // If we hit a wild card, do recursion
    //
    if( *Pattern == '*' ) {

        Pattern++;

        while( *Name && *Pattern ) {

            if( *Name >= 'a' && *Name <= 'z' )
                upcase = *Name - 'a' + 'A';
            else
                upcase = *Name;

            //
            // See if this substring matches
            //
            if( *Pattern == upcase || *Name == '*' ) {

                if( MatchWithPattern( Pattern+1, Name+1 )) {

                    return TRUE;
                }
            }

            //
            // Try the next substring
            //
            Name++;
        }

        //
        // See if match condition was met
        //
        return MatchOkay( Pattern );
    } 

    //
    // Do straight compare until we hit a wild card
    //
    while( *Name && *Pattern != '*' ) {

        if( *Name >= 'a' && *Name <= 'z' )
            upcase = *Name - 'a' + 'A';
        else
            upcase = *Name;

        if( *Pattern == upcase ) {

            Pattern++;
            Name++;

        } else {

            return FALSE;
        }
    }

    //
    // If not done, recurse
    //
    if( *Name ) {

        return MatchWithPattern( Pattern, Name );
    }

    //
    // Make sure its a match
    //
    return MatchOkay( Pattern );
}

//======================================================================
//       B O O T   L O G G I N G   W O R K   R O U T I N E S
//======================================================================

//----------------------------------------------------------------------
//
// RegmonOpenBootLog
//
// Open a log file.
//
//----------------------------------------------------------------------
NTSTATUS RegmonOpenBootLog()
{
    WCHAR                   logFileNameBuffer[] =  L"\\SystemRoot\\REGMON.LOG";
    UNICODE_STRING          logFileUnicodeString;
    OBJECT_ATTRIBUTES       objectAttributes;
    IO_STATUS_BLOCK         ioStatus;
    NTSTATUS                ntStatus;

    RtlInitUnicodeString( &logFileUnicodeString, logFileNameBuffer );
    InitializeObjectAttributes( &objectAttributes, &logFileUnicodeString,
                                OBJ_CASE_INSENSITIVE, NULL, NULL );

    ntStatus = ZwCreateFile( &LogFile, FILE_WRITE_DATA|SYNCHRONIZE,
                             &objectAttributes, &ioStatus, NULL, 
                             FILE_ATTRIBUTE_NORMAL, FILE_SHARE_READ,
                             FILE_OPEN_IF, FILE_SYNCHRONOUS_IO_NONALERT, NULL, 0 );
    return ntStatus;
}

//----------------------------------------------------------------------
//
// RegmonCloseBootLog - worker thread routine
//
// Close the boot log file.
//
//----------------------------------------------------------------------
VOID RegmonCloseBootLog( PVOID Context )
{
    ZwClose( LogFile );
    KeSetEvent( &LoggingEvent, 0, FALSE );
    LogFile = INVALID_HANDLE_VALUE;
}

//----------------------------------------------------------------------
//
// RegmonWriteBuffer
//
// Dumps a buffer to the log file.
//
//----------------------------------------------------------------------
VOID RegmonWriteBuffer( PSTORE_BUF LogStore )
{
    ULONG       len;
    ULONG       itemcnt;
    UCHAR       seqtext[64];
    static CHAR diskFullError[] = "Not enough disk space for log file\n"; 
    PCHAR       textptr, items[10];
    PENTRY      entry;
    FILE_END_OF_FILE_INFORMATION zeroLengthFile;
    IO_STATUS_BLOCK ioStatus;

    //
    // Process the buffer
    //
    for( entry = (PENTRY) LogStore->Data; entry < (PENTRY) ((PCHAR) LogStore + LogStore->Len); ) {
        
        len = strlen( entry->text );
        len += 4; len &= 0xFFFFFFFC;
        
        //
        // Write out the entry. 
        //
        sprintf( seqtext, "%d: ", entry->seq );
        ZwWriteFile( LogFile, NULL, NULL, NULL, &ioStatus,
                     seqtext, strlen(seqtext), NULL, NULL );        
        ZwWriteFile( LogFile, NULL, NULL, NULL, &ioStatus,
                     entry->text, strlen(entry->text), NULL, NULL );
        ZwWriteFile( LogFile, NULL, NULL, NULL, &ioStatus,
                     "\r\n", strlen("\r\n"), NULL, NULL );
            
        //
        // If the disk is full, delete the log file
        // and tell the user there wasn't enough room for it.
        //
        if( ioStatus.Status == STATUS_DISK_FULL ) {

            zeroLengthFile.EndOfFile.QuadPart = 0;
            ZwSetInformationFile( LogFile, &ioStatus, 
                                  &zeroLengthFile, sizeof(zeroLengthFile), FileEndOfFileInformation );
            ZwWriteFile( LogFile, NULL, NULL, NULL, &ioStatus,
                         diskFullError, strlen(diskFullError), NULL, NULL );
            ZwClose( LogFile );
            LogFile = INVALID_HANDLE_VALUE;
            BootLogging = FALSE;
            break;
        }
        entry = (PVOID) (entry->text + len);
    }
}


//----------------------------------------------------------------------
//
// RegmonWriteBootLog - worker thread routine
//
// Writes a buffer out to the log file. We do this in a worker routine
// because the log file handle, which we opened in DriverEntry, is
// only valid in the System process, and worker threads execute in 
// the system process. We are protected by the Store mutex while
// in this procedure, since we are called from NewStore, which 
// is called after the Store mutex is acquired.
//
// NOTE: When Regmon is configured to log activity during a boot it
// is marked to start as the very first driver in the boot sequence.
// Because the SystemRoot symbolic link is not initialized until
// all boot drivers have finished initializing, Regmon is not able
// to open a boot log until some point later. In order that we can
// capture all registry activity we store away output buffers on a list
// until we try and succeed at opening the boot log. When we can we
// send out the accumulated data and then begin dumping buffers
// as they are generated.
//
//----------------------------------------------------------------------
VOID RegmonWriteBootLog( PVOID Context )
{
    PSTORE_BUF  currentStore = Context;
    PSTORE_BUF  saveStore, curSaveStore;
    NTSTATUS    ntStatus;

    //
    // If boot logging is still on, but the log file hasn't been opened,
    // try to open it
    //
    if( BootLogging && LogFile == INVALID_HANDLE_VALUE ) {

        ntStatus = RegmonOpenBootLog();
        
        if( NT_SUCCESS( ntStatus )) {

            //
            // Finally! Process all the buffers we've saved away
            //
            curSaveStore = BootSavedStoreList;
            while( curSaveStore ) {

                RegmonWriteBuffer( curSaveStore );
                BootSavedStoreList = curSaveStore->Next;
                ExFreePool( curSaveStore );
                curSaveStore = BootSavedStoreList;
            }
        }
    }
    
    //
    // Either write out the current buffer or save it away to
    // write out later
    //
    if( LogFile != INVALID_HANDLE_VALUE ) {

        RegmonWriteBuffer( currentStore );

    } else {

        //
        // Save this buffer away until we can successfully open
        // the log file and write it out to disk
        //
        saveStore = ExAllocatePool( PagedPool, sizeof(*saveStore));
        memcpy( saveStore, currentStore, sizeof(*saveStore) );
        saveStore->Next = NULL;
        if( BootSavedStoreList ) {

            BootSavedStoreTail->Next = saveStore;
            BootSavedStoreTail = saveStore;

        } else {
            
            BootSavedStoreList = saveStore;
            BootSavedStoreTail = saveStore;
        }
    }

    //
    // Signal the event
    //
    KeSetEvent( &LoggingEvent, 0, FALSE );
}


//======================================================================
//                   B U F F E R  R O U T I N E S 
//======================================================================

//----------------------------------------------------------------------
//
// RegmonFreeStore
//
// Frees all the data output buffers that we have currently allocated.
//
//----------------------------------------------------------------------
VOID RegmonFreeStore()
{
    PSTORE_BUF      next;
    
    while( Store ) {
        next = Store->Next;
        ExFreePool( Store );
        Store = next;
    }
}       


//----------------------------------------------------------------------
//
// RegmonNewStore
//
// Called when the current buffer has filled up. This moves us to the
// pre-allocated buffer and then allocates another buffer.
//
//----------------------------------------------------------------------
void RegmonNewStore( void )
{
    PSTORE_BUF prev = Store, newstore;
    WORK_QUEUE_ITEM  workItem;

    //
    // If we're boot logging, write the current store out to disk
    //
    if( BootLogging ) {

        ExInitializeWorkItem( &workItem, RegmonWriteBootLog, Store );
        ExQueueWorkItem( &workItem, CriticalWorkQueue );
        KeWaitForSingleObject( &LoggingEvent, Executive, KernelMode, FALSE, NULL );
    }

    //
    // If we have maxed out or haven't accessed the current store
    // just return
    //
    if( MaxStore == NumStore ) {
        Store->Len = 0;
        return; 
    }

    //
    // See if we can re-use a store
    //
    if( !Store->Len ) {

        return;
    }

    //
    // Move to the next buffer and allocate another one
    //
    newstore = ExAllocatePool( PagedPool, sizeof(*Store) );
    if( newstore ) { 

        Store   = newstore;
        Store->Len  = 0;
        Store->Next = prev;
        NumStore++;

    } else {

        Store->Len = 0;

    }
}


//----------------------------------------------------------------------
//
// RegmonOldestStore
//
// Goes through the linked list of storage buffers and returns the 
// oldest one.
//
//----------------------------------------------------------------------
PSTORE_BUF RegmonOldestStore( void )
{
    PSTORE_BUF  ptr = Store, prev = NULL;

    while ( ptr->Next ) {

        ptr = (prev = ptr)->Next;
    }
    if ( prev ) {

        prev->Next = NULL;    
    }
    NumStore--;
    return ptr;
}


//----------------------------------------------------------------------
//
// RegmonResetStore
//
// When a GUI is no longer communicating with us, but we can't unload,
// we reset the storage buffers.
//
//----------------------------------------------------------------------
VOID RegmonResetStore()
{
    PSTORE_BUF  current, next;

    MUTEX_WAIT( StoreMutex );

    //
    // Traverse the list of output buffers
    //
    current = Store->Next;
    while( current ) {

        //
        // Free the buffer
        //
        next = current->Next;
        ExFreePool( current );
        current = next;
    }

    // 
    // Move the output pointer in the buffer that's being kept
    // the start of the buffer.
    // 
    Store->Len = 0;
    Store->Next = NULL;

    MUTEX_RELEASE( StoreMutex );
}



//----------------------------------------------------------------------
//
// UpdateStore
//
// Add a new string to Store, if it fits. 
//
//----------------------------------------------------------------------
void UpdateStore( const char * format, ... )
{       
    PENTRY          Entry;
    ULONG           len;
    va_list         arg_ptr;
    static CHAR     text[MAXPATHLEN*2];

#define A (&format)
    DbgPrint(( (char *)format, A[1], A[2], A[3], A[4], A[5], A[6] ));
    DbgPrint(( "\n" ));
#undef A

    //
    // only do this if a GUI is active
    //
    if( !GUIActive ) return;

    //
    // Lock the buffer pool
    //
    MUTEX_WAIT( StoreMutex );

    //
    // Get a sequence numnber
    //
    InterlockedIncrement( &Sequence );

    //
    // Sprint the string to get the length
    //
    va_start( arg_ptr, format );
    len = vsprintf( text, format, arg_ptr );
    va_end( arg_ptr );    
	len += 4; len &=  0xFFFFFFFC; // +1 to include null terminator and +3 to allign on longword

    //
    // See if its time to switch to extra buffer
    //
    if ( Store->Len + len + sizeof(ENTRY) + 1 >= MAX_STORE ) {

        RegmonNewStore();
    }

    //
    // Store the sequence number so that 
    // a call's result can be paired with its
    // initial data collected when it was made.
    //
    Entry = (void *)(Store->Data+Store->Len);
    Entry->seq = Sequence;
    memcpy( Entry->text, text, len );
    Store->Len += sizeof(Entry->seq)+len;

    //
    // Release the buffer pool
    //
    MUTEX_RELEASE( StoreMutex );
}


//----------------------------------------------------------------------
// 
// strncatZ
//
// Appends a string to another and attaches a null. NT 3.51 ntoskrnl
// does not export this function so we have to make our own, and give
// it a name that won't conflict with the strncat that NT 4.0 exports.
//
//----------------------------------------------------------------------
PCHAR strncatZ( PCHAR dest, PCHAR source, int length )
{       
    int     origlen = strlen(dest);

    strncpy( dest+origlen, source, length );
    dest[ origlen+length ] = 0;
    return(dest);
}

//======================================================================
//                   H A S H  R O U T I N E S 
//======================================================================

//----------------------------------------------------------------------
//
// RegmonHashCleanup
//
// Called when we are unloading to free any memory that we have 
// in our possession.
//
//----------------------------------------------------------------------
VOID RegmonHashCleanup()
{
    PHASH_ENTRY             hashEntry, nextEntry;
    ULONG                   i;

    MUTEX_WAIT( HashMutex );    

    //
    // First free the hash table entries
    //       
    for( i = 0; i < NUMHASH; i++ ) {
        hashEntry = HashTable[i];
        while( hashEntry ) {
            nextEntry = hashEntry->Next;
            ExFreePool( hashEntry->FullPathName );
            ExFreePool( hashEntry );
            hashEntry = nextEntry;
        }
    }
    
    hashEntry = FreeHashList;
    while( hashEntry ) {
        nextEntry = hashEntry->Next;
        ExFreePool( hashEntry );
        hashEntry = nextEntry;
    }
    MUTEX_RELEASE( HashMutex );
}

//----------------------------------------------------------------------
//
// RegmonStoreHash
//
// Stores the key and associated fullpath in the hash table.
//
//----------------------------------------------------------------------
VOID RegmonStoreHash( POBJECT object, PCHAR fullname )
{
    PHASH_ENTRY     newEntry;

    MUTEX_WAIT( HashMutex );

    if( FreeHashList ) {

        newEntry = FreeHashList;
        FreeHashList = newEntry->Next;

    } else {

        newEntry = ExAllocatePool( PagedPool, sizeof(HASH_ENTRY));
    }

    newEntry->Object                = object;
    newEntry->FullPathName          = ExAllocatePool( PagedPool, strlen(fullname)+1 );
    newEntry->Next                  = HashTable[ HASHOBJECT( object) ];
    HashTable[ HASHOBJECT(object) ] = newEntry;     
    strcpy( newEntry->FullPathName, fullname );

    MUTEX_RELEASE( HashMutex );
}


//----------------------------------------------------------------------
//
// RegmonFreeHashEntry
//
// When we see a key close, we can free the string we had associated
// with the fileobject being closed since we know it won't be used
// again.
//
//----------------------------------------------------------------------
VOID RegmonFreeHashEntry( POBJECT object )
{
    PHASH_ENTRY             hashEntry, prevEntry;

    MUTEX_WAIT( HashMutex );

    //
    // look-up the entry
    //
    hashEntry = HashTable[ HASHOBJECT( object ) ];
    prevEntry = NULL;
    while( hashEntry && hashEntry->Object != object ) {
        prevEntry = hashEntry;
        hashEntry = hashEntry->Next;
    }
  
    //
    // If we fall off (didn''t find it), just return
    //
    if( !hashEntry ) {
        MUTEX_RELEASE( HashMutex );
        return;
    }

    //
    // Remove it from the hash list 
    //
    if( prevEntry ) 
        prevEntry->Next = hashEntry->Next;
    else 
        HashTable[ HASHOBJECT( object )] = hashEntry->Next;

    //
    // Free the memory associated with it
    //
    ExFreePool( hashEntry->FullPathName );
    hashEntry->Next = FreeHashList;
    FreeHashList = hashEntry;

    MUTEX_RELEASE( HashMutex );
}

//======================================================================
//  R E G I S T R Y  P A R A M E T E R  S U P P O R T  R O U T I N E S
//======================================================================

//----------------------------------------------------------------------
//
// ConverToUpper
//
// Obvious.
//
//----------------------------------------------------------------------
VOID ConvertToUpper( PCHAR Dest, PCHAR Source, ULONG Len )
{
    ULONG   i;
    
    for( i = 0; i < Len; i++ ) {
        if( Source[i] >= 'a' && Source[i] <= 'z' ) {

            Dest[i] = Source[i] - 'a' + 'A';

        } else {

            Dest[i] = Source[i];
        }
    }
}


//----------------------------------------------------------------------
//
// GetPointer
//
// Translates a handle to an object pointer.
//
//----------------------------------------------------------------------
POBJECT GetPointer( HANDLE handle )
{
    POBJECT         pKey;

    //
    // Ignore null handles
    //
    if( !handle ) return NULL;

    //
    // Get the pointer the handle refers to
    //
    if( ObReferenceObjectByHandle( handle, 0, NULL, KernelMode, &pKey, NULL ) !=
        STATUS_SUCCESS ) {

        DbgPrint(("Error %x getting key pointer\n"));
        pKey = NULL;
    } 
    return pKey;
}


//----------------------------------------------------------------------
//
// ReleasePointer
//
// Dereferences the object.
//
//----------------------------------------------------------------------
VOID ReleasePointer( POBJECT object )
{
    if( object ) ObDereferenceObject( object );
}


//----------------------------------------------------------------------
//
// AppendKeyInformation
//
// Appends key enumerate and query information to the output buffer.
//
//----------------------------------------------------------------------
VOID AppendKeyInformation( IN KEY_INFORMATION_CLASS KeyInformationClass,
                           IN PVOID KeyInformation, PCHAR Buffer )
{
    PKEY_BASIC_INFORMATION  pbasicinfo;
    PKEY_FULL_INFORMATION   pfullinfo;
    PKEY_NODE_INFORMATION   pnodeinfo;
    UNICODE_STRING          ukeyname;       
    ANSI_STRING             akeyname;

    switch( KeyInformationClass ) {

    case KeyBasicInformation:
        pbasicinfo = (PKEY_BASIC_INFORMATION) KeyInformation;
        ukeyname.Length = (USHORT) pbasicinfo->NameLength;
        ukeyname.MaximumLength = (USHORT) pbasicinfo->NameLength;
        ukeyname.Buffer = pbasicinfo->Name;
        RtlUnicodeStringToAnsiString( &akeyname, &ukeyname, TRUE );
        sprintf( Buffer, "Name: %s", akeyname.Buffer );
        RtlFreeAnsiString( &akeyname );
        break;

    case KeyFullInformation:
        pfullinfo = (PKEY_FULL_INFORMATION) KeyInformation;
        sprintf( Buffer, "Subkeys = %d", pfullinfo->SubKeys );
        break;  
        
    case KeyNodeInformation:
        pnodeinfo = (PKEY_NODE_INFORMATION) KeyInformation;
        ukeyname.Length = (USHORT) pnodeinfo->NameLength;
        ukeyname.MaximumLength = (USHORT) pnodeinfo->NameLength;
        ukeyname.Buffer = pnodeinfo->Name;
        RtlUnicodeStringToAnsiString( &akeyname, &ukeyname, TRUE );
        sprintf( Buffer, "Name: %s", akeyname.Buffer );
        RtlFreeAnsiString( &akeyname );
        break;

    default:
        sprintf( Buffer, "Unknown Info Class" );
        break;
    }
}


//----------------------------------------------------------------------
//
// AppendRegValueType
//
// Returns the string form of an registry value type.
//
//----------------------------------------------------------------------
VOID AppendRegValueType( ULONG Type, PCHAR Buffer )
{
    CHAR            tmp[MAXDATALEN];

    switch( Type ) {
    case REG_BINARY:
        strcat( Buffer, "BINARY" );
        break;
    case REG_DWORD_LITTLE_ENDIAN:
        strcat( Buffer, "DWORD_LITTLE_END" );
        break;
    case REG_DWORD_BIG_ENDIAN:
        strcat( Buffer, "DWORD_BIG_END" );
        break;
    case REG_EXPAND_SZ:
        strcat( Buffer, "EXPAND_SZ" );
        break;
    case REG_LINK:
        strcat( Buffer, "LINK" );
        break;
    case REG_MULTI_SZ:
        strcat( Buffer, "MULTI_SZ" );
        break;
    case REG_NONE:
        strcat( Buffer, "NONE" );
        break;
    case REG_SZ:
        strcat( Buffer, "SZ" );
        break;
    case REG_RESOURCE_LIST:
        strcat( Buffer, "RESOURCE_LIST" );
        break;
    case REG_RESOURCE_REQUIREMENTS_LIST:
        strcat( Buffer, "REQ_LIST" );
        break;
    case REG_FULL_RESOURCE_DESCRIPTOR:
        strcat( Buffer, "DESCRIPTOR" );
        break;
    default:
        sprintf( tmp, "UNKNOWN TYPE: %d", Type );
        strcat( Buffer, tmp );
        break;
    }
}


//----------------------------------------------------------------------
//
// AppendRegValueData
//
// We expand certain registry types to provide more information. In
// all cases, calculate the length of the data being copied so 
// we don't overflow the buffer that's passed in. The length of Buffer 
// must be MAXVALLEN.
//
//----------------------------------------------------------------------
VOID AppendRegValueData( IN ULONG Type, IN PVOID Data, IN ULONG Length, 
                         IN OUT PCHAR Buffer )
{
    PWCHAR                  pstring;
    PULONG                  pulong;
    PUCHAR                  pbinary;
    CHAR                    tmp[MAXDATALEN];
    UNICODE_STRING          ukeyname;       
    ANSI_STRING             akeyname;
    int                     len, i;

    switch( Type ) {
    case REG_SZ:    
    case REG_EXPAND_SZ:
    case REG_MULTI_SZ:
        pstring = (PWCHAR) Data;
        ukeyname.Length = (USHORT) Length;
        ukeyname.MaximumLength = (USHORT) Length;
        ukeyname.Buffer = pstring;
        RtlUnicodeStringToAnsiString( &akeyname, 
                                      &ukeyname, TRUE );    
        strcat( Buffer, "\"");
        strncatZ( Buffer+1, akeyname.Buffer, MAXVALLEN - 6);
        if( akeyname.Length > MAXVALLEN - 6 ) strcat( Buffer,"...");
        strcat( Buffer, "\"");
        RtlFreeAnsiString( &akeyname );
        break;

    case REG_DWORD:
        pulong = (PULONG) Data;
        sprintf( tmp, "0x%X", *pulong );
        strcat( Buffer, tmp );
        break;

    case REG_BINARY:
    case REG_RESOURCE_LIST:
    case REG_FULL_RESOURCE_DESCRIPTOR:
    case REG_RESOURCE_REQUIREMENTS_LIST:
        pbinary = (PCHAR) Data;
        if( Length > 8 ) len = 8;
        else len = Length;
        for( i = 0; i < len; i++ ) {
            sprintf( tmp, "%02X ", (UCHAR) pbinary[i]);
            strcat( Buffer, tmp );
        }
        if( Length > 8) strcat( Buffer, "...");
        break;

    default:
        AppendRegValueType( Type, Buffer );
        break;
    }
}


//----------------------------------------------------------------------
//
// AppendValueInformation
//
// Appends value enumerate and query information to the output buffer.
//
//----------------------------------------------------------------------
VOID AppendValueInformation( IN KEY_VALUE_INFORMATION_CLASS KeyValueInformationClass,
                             IN PVOID KeyValueInformation, PCHAR Buffer, PCHAR ValueName )
{
    PKEY_VALUE_BASIC_INFORMATION    pbasicinfo;
    PKEY_VALUE_FULL_INFORMATION     pfullinfo;
    PKEY_VALUE_PARTIAL_INFORMATION  ppartinfo;
    UNICODE_STRING                  ukeyname;       
    ANSI_STRING                     akeyname;

    switch( KeyValueInformationClass ) {

    case KeyValueBasicInformation:
        pbasicinfo = (PKEY_VALUE_BASIC_INFORMATION)
            KeyValueInformation;
        sprintf( Buffer, "Type: ");
        AppendRegValueType( pbasicinfo->Type, Buffer );
        strncatZ( Buffer, " Name: ", MAXVALLEN - 1 - strlen(Buffer) );
        ukeyname.Length = (USHORT) pbasicinfo->NameLength;
        ukeyname.MaximumLength = (USHORT) pbasicinfo->NameLength;
        ukeyname.Buffer = pbasicinfo->Name;
        RtlUnicodeStringToAnsiString( &akeyname, &ukeyname, TRUE );
        strncatZ( Buffer, akeyname.Buffer, MAXVALLEN - 1 - strlen(Buffer) );
        if( ValueName ) strncpy( ValueName, akeyname.Buffer, MAXVALLEN - 1 );
        RtlFreeAnsiString( &akeyname );                 
        break;

    case KeyValueFullInformation:   
        pfullinfo = (PKEY_VALUE_FULL_INFORMATION) 
            KeyValueInformation;
        AppendRegValueData( pfullinfo->Type, 
                            (PVOID) ((PCHAR) pfullinfo + pfullinfo->DataOffset), 
                            pfullinfo->DataLength, Buffer );
        if( ValueName ) {
            ukeyname.Length = (USHORT) pfullinfo->NameLength;
            ukeyname.MaximumLength = (USHORT) pfullinfo->NameLength;
            ukeyname.Buffer = pfullinfo->Name;
            RtlUnicodeStringToAnsiString( &akeyname, &ukeyname, TRUE );
            strncpy( ValueName, akeyname.Buffer, MAXVALLEN - 1 );
            RtlFreeAnsiString( &akeyname ); 
        }
        break;

    case KeyValuePartialInformation:
        ppartinfo = (PKEY_VALUE_PARTIAL_INFORMATION)
            KeyValueInformation;
        AppendRegValueData( ppartinfo->Type, 
                            (PVOID) ppartinfo->Data, 
                            ppartinfo->DataLength, Buffer );
        break;

    default:
        sprintf( Buffer, "Unknown Info Class" );
        break;
    }
}

//----------------------------------------------------------------------
//
// ErrorString
//
// Returns the string form of an error code.
//
//----------------------------------------------------------------------
PCHAR ErrorString( NTSTATUS retval )
{
    //
    // Before transating, apply error filter
    //
    if( retval == STATUS_SUCCESS && !FilterDef.logsuccess ) return NULL;
    if( retval != STATUS_SUCCESS && !FilterDef.logerror   ) return NULL;

    //
    // Passed filter, so log it
    //
    switch( retval ) {
    case STATUS_BUFFER_TOO_SMALL:
        return "BUFTOOSMALL";
    case STATUS_SUCCESS:
        return "SUCCESS";
    case STATUS_KEY_DELETED:
        return "KEYDELETED";
    case STATUS_REGISTRY_IO_FAILED:
        return "IOFAILED";
    case STATUS_REGISTRY_CORRUPT:
        return "CORRUPT";
    case STATUS_NO_MEMORY:
        return "OUTOFMEM";
    case STATUS_ACCESS_DENIED:
        return "ACCDENIED";
    case STATUS_NO_MORE_ENTRIES:
        return "NOMORE";
    case STATUS_OBJECT_NAME_NOT_FOUND:
        return "NOTFOUND";
    case STATUS_BUFFER_OVERFLOW:
        return "BUFOVRFLOW";
    case STATUS_OBJECT_PATH_SYNTAX_BAD:
        return "SYNTAXERR";
    default:
        sprintf(errstring, "%x", retval );
        return errstring;
    }
}


//----------------------------------------------------------------------
//
// RegmonFreeFilters
//
// Fress storage we allocated for filter strings.
//
//----------------------------------------------------------------------
VOID RegmonFreeFilters()
{
    ULONG   i;

    for( i = 0; i < NumProcessFilters; i++ ) {

        ExFreePool( ProcessFilters[i] );
    }
    for( i = 0; i < NumProcessExcludeFilters; i++ ) {

        ExFreePool( ProcessExcludeFilters[i] );
    }
    for( i = 0; i < NumPathIncludeFilters; i++ ) {

        ExFreePool( PathIncludeFilters[i] );
    }
    for( i = 0; i < NumPathExcludeFilters; i++ ) {

        ExFreePool( PathExcludeFilters[i] );
    }
    NumProcessFilters = 0;
    NumProcessExcludeFilters = 0;
    NumPathIncludeFilters = 0;
    NumPathExcludeFilters = 0;
}

//----------------------------------------------------------------------
//
// MakeFilterArray
//
// Takes a filter string and splits into components (a component
// is seperated with a ';')
//
//----------------------------------------------------------------------
VOID MakeFilterArray( PCHAR FilterString,
                      PCHAR FilterArray[],
                      PULONG NumFilters )
{
    PCHAR filterStart;
    ULONG filterLength;

    //
    // Scan through the process filters
    //
    filterStart = FilterString;
    while( *filterStart ) {

        filterLength = 0;
        while( filterStart[filterLength] &&
               filterStart[filterLength] != ';' ) {

            filterLength++;
        }

        //
        // Ignore zero-length components
        //
        if( filterLength ) {

            FilterArray[ *NumFilters ] = 
                ExAllocatePool( PagedPool, filterLength + 1 );
            strncpy( FilterArray[ *NumFilters ],
                     filterStart, filterLength );
            FilterArray[ *NumFilters ][filterLength] = 0;
            (*NumFilters)++;
        }
    
        //
        // Are we done?
        //
        if( !filterStart[filterLength] ) break;

        //
        // Move to the next component (skip over ';')
        //
        filterStart += filterLength + 1;
    }
}

//----------------------------------------------------------------------
//
// RegmonUpdateFilters
//
// Takes a new filter specification and updates the filter
// arrays with them.
//
//----------------------------------------------------------------------
VOID RegmonUpdateFilters()
{
    //
    // Free old filters (if any)
    //
    MUTEX_WAIT( FilterMutex );

    RegmonFreeFilters();

    //
    // Create new filter arrays
    //
    MakeFilterArray( FilterDef.processfilter,
                     ProcessFilters, &NumProcessFilters );
    MakeFilterArray( FilterDef.processexclude,
                     ProcessExcludeFilters, &NumProcessExcludeFilters );
    MakeFilterArray( FilterDef.pathfilter,
                     PathIncludeFilters, &NumPathIncludeFilters );
    MakeFilterArray( FilterDef.excludefilter,
                     PathExcludeFilters, &NumPathExcludeFilters );    

    MUTEX_RELEASE( FilterMutex );
}


//----------------------------------------------------------------------
//
// ApplyNameFilter
//
// If the name matches the exclusion mask, we do not log it. Else if
// it doesn't match the inclusion mask we do not log it. 
//
//----------------------------------------------------------------------
BOOLEAN ApplyNameFilter( PCHAR fullname )
{
    ULONG    i;

    //   
    // If it matches the exclusion string, do not log it
    //
    MUTEX_WAIT( FilterMutex );

    for( i = 0; i < NumPathExcludeFilters; i++ ) {

        if( MatchWithPattern( PathExcludeFilters[i], fullname ) ) {

            MUTEX_RELEASE( FilterMutex );
            return FALSE;
        }
    }
 
    //
    // If it matches an include filter then log it
    //
    for( i = 0; i < NumPathIncludeFilters; i++ ) {

        if( MatchWithPattern( PathIncludeFilters[i], fullname )) {

            MUTEX_RELEASE( FilterMutex );
            return TRUE;
        }
    }

    //
    // It didn't match any include filters so don't log
    //
    MUTEX_RELEASE( FilterMutex );
    return FALSE;
}

//----------------------------------------------------------------------
//
// GetFullName
//
// Returns the full pathname of a key, if we can obtain one, else
// returns a handle.
//
//----------------------------------------------------------------------
void GetFullName( HANDLE hKey, PUNICODE_STRING lpszSubKeyVal, 
                  PCHAR fullname )
{
    PHASH_ENTRY             hashEntry;
    POBJECT                 pKey = NULL;
    CHAR                    tmpkey[16];
    ANSI_STRING             keyname;
    PCHAR                   tmpname;
    CHAR                    cmpname[MAXROOTLEN];
    PCHAR                   nameptr;
    PUNICODE_STRING         fullUniName;
    ULONG                   actualLen;
    int                     i;

    //
    // Allocate a temporary buffer
    //
    tmpname = ExAllocatePool( PagedPool, MAXPATHLEN );

    //
    // Translate the hkey into a pointer
    //
    fullname[0] = 0;
    tmpname[0] = 0;

    //
    // Is it a valid handle?
    //
    if( pKey = GetPointer( hKey )) {

        //
        // See if we find the key in the hash table
        //
        ReleasePointer( pKey );
        MUTEX_WAIT( HashMutex );
        hashEntry = HashTable[ HASHOBJECT( pKey ) ];
        while( hashEntry && hashEntry->Object != pKey )
            hashEntry = hashEntry->Next;
        MUTEX_RELEASE( HashMutex );

        if( hashEntry ) {

            strcpy( tmpname, hashEntry->FullPathName );

        } else {

            //
            // We will only get here if key was created before we loaded - ask the Configuration
            // Manager what the name of the key is.
            //
            if( pKey ) {

                fullUniName = ExAllocatePool( PagedPool, MAXPATHLEN*2+2*sizeof(ULONG));
                fullUniName->MaximumLength = MAXPATHLEN*2;
        
                if( NT_SUCCESS(ObQueryNameString( pKey, fullUniName, MAXPATHLEN, &actualLen ) )) {

                    RtlUnicodeStringToAnsiString( &keyname, fullUniName, TRUE ); 
                    if( keyname.Buffer[0] ) {         
                        strcpy( tmpname, "\\" );
                        strncatZ( tmpname, keyname.Buffer, MAXPATHLEN -2 );
                    }
                    RtlFreeAnsiString( &keyname );
                }
                ExFreePool( fullUniName );
            }
        }
    }

    //
    // Append subkey and value, if they are there
    //
    if( lpszSubKeyVal ) {
        RtlUnicodeStringToAnsiString( &keyname, lpszSubKeyVal, TRUE );
        if( keyname.Buffer[0] ) {
            strcat( tmpname, "\\" );
            strncatZ( tmpname, keyname.Buffer, MAXPATHLEN - 1 - strlen(tmpname) );
        }
        RtlFreeAnsiString( &keyname );
    }

    //
    // See if it matches current user
    //
    for( i = 0; i < 2; i++ ) {
        ConvertToUpper( cmpname, tmpname, CurrentUser[i].RootNameLen );
        if( !strncmp( cmpname, CurrentUser[i].RootName,
                      CurrentUser[i].RootNameLen )) {

            DbgPrint(( " CurrentUser(%d) %s ==> %s\n", i, 
                       tmpname, CurrentUser[i].RootName ));

            //
            // Its current user. Process to next slash
            //
            nameptr = tmpname + CurrentUser[i].RootNameLen;
            while( *nameptr && *nameptr != '\\' ) nameptr++;
            strcpy( fullname, CurrentUser[i].RootShort );
            strcat( fullname, nameptr );
            ExFreePool( tmpname );
            return;
        }
    }     

    //
    // Now, see if we can translate a root key name
    //
    for( i = 0; i < NUMROOTKEYS; i++ ) {
        ConvertToUpper( cmpname, tmpname, RootKey[i].RootNameLen );
        if( !strncmp( cmpname, RootKey[i].RootName, 
                      RootKey[i].RootNameLen )) {
            nameptr = tmpname + RootKey[i].RootNameLen;
            strcpy( fullname, RootKey[i].RootShort );
            strcat( fullname, nameptr );
            ExFreePool( tmpname );
            return;
        }
    }

    //
    // No translation
    //
    strcpy( fullname, tmpname );
    ExFreePool( tmpname ); 
}


//----------------------------------------------------------------------
//
// GetProcessNameOffset
//
// In an effort to remain version-independent, rather than using a
// hard-coded into the KPEB (Kernel Process Environment Block), we
// scan the KPEB looking for the name, which should match that
// of the GUI process
//
//----------------------------------------------------------------------
ULONG GetProcessNameOffset()
{
    PEPROCESS       curproc;
    int             i;

    curproc = PsGetCurrentProcess();

    //
    // Scan for 12KB, hopping the KPEB never grows that big!
    //
    for( i = 0; i < 3*PAGE_SIZE; i++ ) {
     
        if( !strncmp( SYSNAME, (PCHAR) curproc + i, strlen(SYSNAME) )) {

            return i;
        }
    }

    //
    // Name not found - oh, well
    //
    return 0;
}



//----------------------------------------------------------------------
//
// GetProcess
//
// Uses undocumented data structure offsets to obtain the name of the
// currently executing process.
//
//----------------------------------------------------------------------
PCHAR GetProcess( PCHAR Name )
{
    PEPROCESS       curproc;
    char            *nameptr;
    ULONG           i;

    //
    // We only try and get the name if we located the name offset
    //
    if( ProcessNameOffset ) {
    
        curproc = PsGetCurrentProcess();
        nameptr   = (PCHAR) curproc + ProcessNameOffset;
        strncpy( Name, nameptr, 16 );

    } else {
     
        strcpy( Name, "???");
    }

    //
    // Apply process name filters
    //
    MUTEX_WAIT( FilterMutex );
    for( i = 0; i < NumProcessExcludeFilters; i++ ) {

        if( MatchWithPattern( ProcessExcludeFilters[i], Name )) {

            MUTEX_RELEASE( FilterMutex );
            return NULL;
        }
    }
    for( i = 0; i < NumProcessFilters; i++ ) {

        if( MatchWithPattern( ProcessFilters[i], Name ) ) {

            MUTEX_RELEASE( FilterMutex );
            return Name;
        }
    }
    MUTEX_RELEASE( FilterMutex );
    return NULL;
}

//======================================================================
//                    H O O K  R O U T I N E S
//======================================================================

//----------------------------------------------------------------------
//
// HookRegOpenKey
//
//----------------------------------------------------------------------
NTSTATUS HookRegOpenKey( IN OUT PHANDLE pHandle, IN ACCESS_MASK ReqAccess, 
                         IN POBJECT_ATTRIBUTES pOpenInfo )
{
    NTSTATUS                ntstatus;
    POBJECT                 regobj;
    CHAR                    fullname[MAXPATHLEN], data[MAXDATALEN], name[MAXPROCNAMELEN];

    GetFullName( pOpenInfo->RootDirectory, pOpenInfo->ObjectName, fullname );
    ntstatus = RealRegOpenKey( pHandle, ReqAccess, pOpenInfo );
    DbgPrint(("RegOpenKey: %s => %x, %x\n", fullname, *pHandle, ntstatus ));
    data[0] = 0;
    if( NT_SUCCESS( ntstatus )) {   
        regobj = GetPointer( *pHandle );
        RegmonFreeHashEntry( regobj );
        RegmonStoreHash( regobj, fullname );
        sprintf(data,"Key: 0x%X", regobj );
        ReleasePointer( regobj );
    }
    if( FilterDef.logreads && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tOpenKey\t%s\t%s\t%s", name,
                     fullname, ErrorString( ntstatus ), data );
    }
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegCreateKey
//
//----------------------------------------------------------------------
NTSTATUS HookRegCreateKey( OUT PHANDLE pHandle, IN ACCESS_MASK ReqAccess,
                           IN POBJECT_ATTRIBUTES pOpenInfo, IN ULONG TitleIndex,
                           IN PUNICODE_STRING Class, IN ULONG CreateOptions, OUT PULONG Disposition )
{
    NTSTATUS                ntstatus;
    POBJECT                 regobj;
    CHAR                    fullname[MAXPATHLEN], data[MAXDATALEN], name[MAXPROCNAMELEN];

    GetFullName( pOpenInfo->RootDirectory, pOpenInfo->ObjectName, fullname );
	ntstatus = RealRegCreateKey( pHandle, ReqAccess, pOpenInfo, TitleIndex,
                                 Class, CreateOptions, Disposition );
    DbgPrint(("RegCreateKey: %s => %x, %x\n", fullname, *pHandle, ntstatus ));
    data[0] = 0;
    if( NT_SUCCESS( ntstatus )) {   
        regobj = GetPointer( *pHandle );
        RegmonFreeHashEntry( regobj );
        RegmonStoreHash( regobj, fullname );
        sprintf(data,"Key: 0x%X", regobj );
        ReleasePointer( regobj );
    }
    if( ((NT_SUCCESS( ntstatus ) && 
          (Disposition && *Disposition == REG_CREATED_NEW_KEY && FilterDef.logwrites)) ||
         FilterDef.logreads ) && 
        GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tCreateKey\t%s\t%s\t%s", name,
                     fullname, ErrorString( ntstatus ), data);
    }
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegCloseKey
//
// This is actually a hook for NtClose which is used for closing any
// object. Therefore, we must ensure that we are seeing a close for 
// a registry object that we know about.
//
//----------------------------------------------------------------------
NTSTATUS HookRegCloseKey( IN HANDLE Handle )
{
    NTSTATUS                ntstatus;
    POBJECT                 regobj;
    CHAR                    name[MAXPROCNAMELEN];
    PCHAR                   fullname, data;
    ULONG                   retlen;
    BOOLEAN                 iskey = FALSE;
    KEY_BASIC_INFORMATION   basicInfo;
    
    //
    // Allocate data from pool since this close routine can be called from other
    // drivers, where the stack space may already be strained
    //
    fullname = ExAllocatePool( PagedPool, MAXPATHLEN );
    data     = ExAllocatePool( PagedPool, MAXVALLEN );

    //
    // Determine if the object is a key by querying it
    //
    ntstatus = RealRegQueryKey( Handle, KeyBasicInformation, 
                                &basicInfo, 0, &retlen );
    if( ntstatus != STATUS_OBJECT_TYPE_MISMATCH ) {
        iskey = TRUE;        
        GetFullName( Handle, NULL, fullname );

        // get the pointer for later
        regobj = GetPointer( Handle );
        ReleasePointer( regobj );
    }

    ntstatus = RealRegCloseKey( Handle );
    if( iskey ) {
        DbgPrint(("RegCloseKey: %s => %x, %x\n", fullname, Handle, ntstatus ));
        data[0] = 0;
        if( NT_SUCCESS( ntstatus )) {
            if( regobj ) RegmonFreeHashEntry( regobj );
            sprintf(data,"Key: 0x%X", regobj );
            if( FilterDef.logreads && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
                UpdateStore( "%s\tCloseKey\t%s\t%s\t%s", 
                             name, fullname, ErrorString( ntstatus ), data );
            }
        }
    }

    ExFreePool( fullname );
    ExFreePool( data );
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegFlushKey
//
//----------------------------------------------------------------------
NTSTATUS HookRegFlushKey( IN HANDLE Handle )
{
    NTSTATUS                ntstatus;
    CHAR                    fullname[MAXPATHLEN], name[MAXPROCNAMELEN];
    POBJECT                 regobj;

    GetFullName( Handle, NULL, fullname );
    ntstatus = RealRegFlushKey( Handle );
    DbgPrint(("RegFlushKey: %s => 0x%X\n", fullname, ntstatus ));
    regobj = GetPointer( Handle );
    ReleasePointer( regobj );
    if( FilterDef.logwrites && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tFlushKey\t%s\t%s\tKey: 0x%X", 
                     name, fullname, ErrorString( ntstatus ), regobj);
    }
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegDeleteKey
//
// Once we've deleted a key, we can remove its reference in the hash 
// table.
//
//----------------------------------------------------------------------
NTSTATUS HookRegDeleteKey( IN HANDLE Handle )
{
    NTSTATUS                ntstatus;
    POBJECT                 regobj;
    CHAR                    fullname[MAXPATHLEN], name[MAXPROCNAMELEN];

    GetFullName( Handle, NULL, fullname );
    regobj = GetPointer( Handle );
    ReleasePointer( regobj );
    ntstatus = RealRegDeleteKey( Handle );
    DbgPrint(("RegDeleteKey: %s => 0x%X\n", fullname, ntstatus ));
    if( FilterDef.logwrites && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tDeleteKey\t%s\t%s\tKey: 0x%X", 
                     name, fullname, 
                     ErrorString( ntstatus ), regobj);
    }
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegDeleteValueKey
//
//----------------------------------------------------------------------
NTSTATUS HookRegDeleteValueKey( IN HANDLE Handle, PUNICODE_STRING Name )
{
    NTSTATUS                ntstatus;
    CHAR                    fullname[MAXPATHLEN], name[MAXPROCNAMELEN];

    GetFullName( Handle, Name, fullname );
    ntstatus = RealRegDeleteValueKey( Handle, Name );
    DbgPrint(("RegDeleteValueKey: %s => %x\n", fullname, ntstatus ));
    if( FilterDef.logwrites && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus ) ) {
        UpdateStore( "%s\tDeleteValueKey\t%s\t%s\t", 
                     name, fullname, ErrorString( ntstatus ));
    }
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegSetValueKey
//
//---------------------------------------------------------------------- 
NTSTATUS HookRegSetValueKey( IN HANDLE KeyHandle, IN PUNICODE_STRING ValueName,
                             IN ULONG TitleIndex, IN ULONG Type, IN PVOID Data, IN ULONG DataSize )
{
    NTSTATUS                ntstatus;
    PUNICODE_STRING         valueName;
    CHAR                    fullname[MAXPATHLEN], data[MAXVALLEN], name[MAXPROCNAMELEN];

    if( !ValueName || !ValueName->Length ) valueName = &DefaultValue;
    else                                   valueName = ValueName;
    GetFullName( KeyHandle, valueName, fullname );
    ntstatus = RealRegSetValueKey( KeyHandle, ValueName, TitleIndex,
                                   Type, Data, DataSize );
    data[0] = 0;
    if( NT_SUCCESS( ntstatus )) 
        AppendRegValueData( Type, Data, DataSize, data );
    DbgPrint(("SetValue: %s (%s)\n", fullname, data ));
    if( FilterDef.logwrites && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tSetValue\t%s\t%s\t%s", 
                     name, fullname, ErrorString( ntstatus ), data );
    }
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegEnumerateKey
//
// This is a documented Zw-class function. 
//
//----------------------------------------------------------------------
NTSTATUS HookRegEnumerateKey( IN HANDLE KeyHandle, IN ULONG Index,
                              IN KEY_INFORMATION_CLASS KeyInformationClass,
                              OUT PVOID KeyInformation, IN ULONG Length, OUT PULONG pResultLength )
{
    NTSTATUS                ntstatus;
    CHAR                    fullname[MAXPATHLEN], data[MAXVALLEN], name[MAXPROCNAMELEN];

    GetFullName( KeyHandle, NULL, fullname );
    ntstatus = RealRegEnumerateKey( KeyHandle, Index, KeyInformationClass,
                                    KeyInformation, Length, pResultLength );
    data[0] = 0;
    if( NT_SUCCESS( ntstatus )) 
        AppendKeyInformation( KeyInformationClass, KeyInformation, data );

    DbgPrint(("EnumerateKey: %s (%s) => %x\n", fullname, data, ntstatus ));
    if( FilterDef.logreads && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tEnumerateKey\t%s\t%s\t%s", 
                     name, fullname, ErrorString( ntstatus ), data );
    }
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegQueryKey
//
// This is a documented Zw-class function. This will get called
// from our CloseKey hook routine, because this is the only easy
// way we can determine if a registry key is being closed. Thus, we
// have to watch for those calls and not log any data about them.
//
//----------------------------------------------------------------------
NTSTATUS HookRegQueryKey( IN HANDLE  KeyHandle, 
                          IN KEY_INFORMATION_CLASS  KeyInformationClass,
                          OUT PVOID  KeyInformation, IN ULONG  Length, 
                          OUT PULONG  pResultLength )
{
    NTSTATUS                ntstatus;
    CHAR                    name[MAXPROCNAMELEN];
    PCHAR                   fullname, data;

    //
    // Allocate data from pool since this routine is called from the HookRegClose routine, 
    // which is called on non-key object and so is likely to be originating in a driver
    // that may already have strained stack space.
    //
    fullname = ExAllocatePool( PagedPool, MAXPATHLEN );
    data     = ExAllocatePool( PagedPool, MAXVALLEN );

    GetFullName( KeyHandle, NULL, fullname );

    ntstatus = RealRegQueryKey( KeyHandle, KeyInformationClass,
                                KeyInformation, Length, pResultLength );

    // print out different stuff depending on type of info asked for
    data[0] = 0;
    if( NT_SUCCESS( ntstatus )) 
        AppendKeyInformation( KeyInformationClass, KeyInformation, data );

    DbgPrint(("QueryKey: %s (%s) => %x\n", fullname, data, ntstatus ));
    if( FilterDef.logreads && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tQueryKey\t%s\t%s\t%s", 
                     name, fullname, ErrorString( ntstatus ), data );
    }

    ExFreePool( fullname );
    ExFreePool( data );
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegEnumerateValueKey
//
// This is a documented Zw-class function.
//
//----------------------------------------------------------------------
NTSTATUS HookRegEnumerateValueKey( IN HANDLE KeyHandle, IN ULONG Index,
                                   IN KEY_VALUE_INFORMATION_CLASS KeyValueInformationClass,
                                   OUT PVOID KeyValueInformation, IN ULONG Length,
                                   OUT PULONG  pResultLength )
{
    NTSTATUS                ntstatus;
    CHAR                    fullname[MAXPATHLEN], data[MAXVALLEN]; 
    CHAR                    valuename[MAXVALLEN], name[MAXPROCNAMELEN];

    GetFullName( KeyHandle, NULL, fullname );
    ntstatus = RealRegEnumerateValueKey( KeyHandle, Index,
                                         KeyValueInformationClass,
                                         KeyValueInformation, Length, 
                                         pResultLength );
    data[0] = 0;

    if( NT_SUCCESS( ntstatus )) {
        AppendValueInformation( KeyValueInformationClass, 
                                KeyValueInformation, data, valuename );
        strcat( fullname, "\\" );
        strncatZ( fullname, valuename, MAXPATHLEN - 1 - strlen(fullname) );
    }

	DbgPrint(("EnumerateValue: %s (%s) =>%x\n", fullname, data, ntstatus ));
    if( FilterDef.logreads && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tEnumerateValue\t%s\t%s\t%s", 
                     name, fullname, ErrorString( ntstatus ), data );
    }

    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegQueryValueKey
//
// This is a documented Zw-class function.
//
//----------------------------------------------------------------------
NTSTATUS HookRegQueryValueKey( IN HANDLE KeyHandle,
                               IN PUNICODE_STRING ValueName,
                               IN KEY_VALUE_INFORMATION_CLASS KeyValueInformationClass,
                               OUT PVOID KeyValueInformation, IN ULONG Length,
                               OUT PULONG  pResultLength )
{
    NTSTATUS                ntstatus;
    PUNICODE_STRING         valueName;
    CHAR                    fullname[MAXPATHLEN], data[MAXVALLEN], name[MAXPROCNAMELEN];

    if( !ValueName || !ValueName->Length ) valueName = &DefaultValue;
    else                                   valueName = ValueName;
    GetFullName( KeyHandle, valueName, fullname );
    ntstatus = RealRegQueryValueKey( KeyHandle, ValueName,
                                     KeyValueInformationClass,
                                     KeyValueInformation, Length, 
                                     pResultLength );
    data[0] = 0;
    if( NT_SUCCESS( ntstatus )) 
        AppendValueInformation( KeyValueInformationClass, 
                                KeyValueInformation, data, FALSE );
    DbgPrint(("QueryValue: %s (%s) =>%x\n", fullname, data, ntstatus ));
    if( FilterDef.logreads && GetProcess( name ) && ApplyNameFilter(fullname) && ErrorString( ntstatus )) {
        UpdateStore( "%s\tQueryValue\t%s\t%s\t%s", 
                     name, fullname, ErrorString( ntstatus ), data );
    }
    return ntstatus;
}


//----------------------------------------------------------------------
//
// HookRegistry
//
// Replaces entries in the system service table with pointers to
// our own hook routines. We save off the real routine addresses.
//
//----------------------------------------------------------------------
VOID HookRegistry( void )
{
    if( !RegHooked ) {

        //
        // Hook everything
        //

        RealRegOpenKey = SYSCALL( ZwOpenKey );
        SYSCALL( ZwOpenKey ) = (PVOID) HookRegOpenKey;

        RealRegQueryKey = SYSCALL( ZwQueryKey );
        SYSCALL( ZwQueryKey ) = (PVOID) HookRegQueryKey;

        RealRegQueryValueKey = SYSCALL( ZwQueryValueKey );
        SYSCALL( ZwQueryValueKey ) = (PVOID) HookRegQueryValueKey;

        RealRegEnumerateValueKey = SYSCALL( ZwEnumerateValueKey );
        SYSCALL( ZwEnumerateValueKey ) = (PVOID) HookRegEnumerateValueKey;

        RealRegEnumerateKey = SYSCALL( ZwEnumerateKey );
        SYSCALL( ZwEnumerateKey ) = (PVOID) HookRegEnumerateKey;

        RealRegDeleteKey = SYSCALL( ZwDeleteKey );
        SYSCALL( ZwDeleteKey ) = (PVOID) HookRegDeleteKey;

        RealRegFlushKey = SYSCALL( ZwFlushKey );
        SYSCALL( ZwFlushKey ) = (PVOID) HookRegFlushKey;

        RealRegSetValueKey = SYSCALL( ZwSetValueKey );
        SYSCALL( ZwSetValueKey ) = (PVOID) HookRegSetValueKey;

        RealRegCreateKey = SYSCALL( ZwCreateKey );
#if defined(_ALPHA_)
        SYSCALL( ZwCreateKey ) = (PVOID) ((ULONG) HookRegCreateKey + ((ULONG) RealRegCreateKey & 0x00000003));
#else
        SYSCALL( ZwCreateKey ) = (PVOID) HookRegCreateKey;
#endif

        RealRegDeleteValueKey = SYSCALL( ZwDeleteValueKey );
        SYSCALL( ZwDeleteValueKey ) = (PVOID) HookRegDeleteValueKey;

        RealRegCloseKey = SYSCALL( ZwClose );
        SYSCALL( ZwClose ) = (PVOID) HookRegCloseKey;

        RegHooked = TRUE;

    }
}


//----------------------------------------------------------------------
//
// UnhookRegistry
//
// Unhooks all registry routines by replacing the hook addresses in 
// the system service table with the real routine addresses that we
// saved off.
//
//----------------------------------------------------------------------
VOID UnhookRegistry( )
{
    if( RegHooked ) {

        //
        // Unhook everything
        //
        SYSCALL( ZwOpenKey ) = (PVOID) RealRegOpenKey;
        SYSCALL( ZwQueryKey ) = (PVOID) RealRegQueryKey;
        SYSCALL( ZwQueryValueKey ) = (PVOID) RealRegQueryValueKey;
        SYSCALL( ZwEnumerateValueKey ) = (PVOID) RealRegEnumerateValueKey;
        SYSCALL( ZwEnumerateKey ) = (PVOID) RealRegEnumerateKey;
        SYSCALL( ZwClose ) = (PVOID) RealRegCloseKey;
        SYSCALL( ZwFlushKey ) = (PVOID) RealRegFlushKey;
        SYSCALL( ZwDeleteKey ) = (PVOID) RealRegDeleteKey;
        SYSCALL( ZwSetValueKey ) = (PVOID) RealRegSetValueKey;
        SYSCALL( ZwCreateKey ) = (PVOID) RealRegCreateKey;
        SYSCALL( ZwDeleteValueKey ) = (PVOID) RealRegDeleteValueKey;

        RegHooked = FALSE;
    }
}

//======================================================================
//         D E V I C E - D R I V E R  R O U T I N E S 
//======================================================================

//----------------------------------------------------------------------
//
// RegmonDeviceControl
//
//----------------------------------------------------------------------
BOOLEAN  RegmonDeviceControl( IN PFILE_OBJECT FileObject, IN BOOLEAN Wait,
                              IN PVOID InputBuffer, IN ULONG InputBufferLength, 
                              OUT PVOID OutputBuffer, IN ULONG OutputBufferLength, 
                              IN ULONG IoControlCode, OUT PIO_STATUS_BLOCK IoStatus, 
                              IN PDEVICE_OBJECT DeviceObject ) {
    BOOLEAN                 retval = FALSE;
    PSTORE_BUF              old;

    //
    // Its a message from our GUI!
    //
    IoStatus->Status      = STATUS_SUCCESS; // Assume success
    IoStatus->Information = 0;              // Assume nothing returned
    switch ( IoControlCode ) {

    case REGMON_version:

        //
        // Version #
        //
        if ( OutputBufferLength >= sizeof(ULONG) ) {

            *(ULONG *)OutputBuffer = REGMONVERSION;
            IoStatus->Information = sizeof(ULONG);

        } else {

            IoStatus->Status = STATUS_INVALID_PARAMETER;
        }
        break;

    case REGMON_hook:
        DbgPrint (("Regmon: hook\n"));
        HookRegistry();
        break;

    case REGMON_unhook:
        DbgPrint(("Regmon: unhook\n"));
        UnhookRegistry();
        break;

    case REGMON_zerostats:

        //
        // Zero contents of buffer
        //
        DbgPrint (("Regmon: zero stats\n"));
        MUTEX_WAIT( StoreMutex );
        while ( Store->Next )  {
            // release next
            old = Store->Next;
            Store->Next = old->Next;
            MUTEX_WAIT( StoreMutex );
            ExFreePool( old );
            NumStore--;
            MUTEX_RELEASE( StoreMutex );
        }
        Store->Len = 0;
        Sequence = 0;
        MUTEX_RELEASE( StoreMutex );
        break;

    case REGMON_getstats:

        //
        // Copy buffer into user space.
        //
        DbgPrint (("Regmon: get stats\n"));

        //
        // Probe the output buffer
        //
        try {                 

            ProbeForWrite( OutputBuffer,
                           OutputBufferLength,
                           sizeof( UCHAR ));

        } except( EXCEPTION_EXECUTE_HANDLER ) {

            IoStatus->Status = STATUS_INVALID_PARAMETER;
            return FALSE;
        }            

        MUTEX_WAIT( StoreMutex );
        if ( MAX_STORE > OutputBufferLength )  {

            //
            // Output buffer isn't big enough
            //
            MUTEX_RELEASE( StoreMutex );
            IoStatus->Status = STATUS_BUFFER_TOO_SMALL;
            return FALSE;

        } else if ( Store->Len  ||  Store->Next ) {

            //
            // Switch to a new store
            //
            RegmonNewStore();

            // Fetch the oldest to give to user
            old = RegmonOldestStore();
            MUTEX_RELEASE( StoreMutex );

            //
            // Copy it
            //
            memcpy( OutputBuffer, old->Data, old->Len );

            //
            // Return length of copied info
            //
            IoStatus->Information = old->Len;

            //
            // Deallocate buffer
            //
            ExFreePool( old );

        } else {
            //
            // No unread data
            //
            MUTEX_RELEASE( StoreMutex );
            IoStatus->Information = 0;
        }
        break;

    case REGMON_setfilter:
        //        
        // GUI is updating the filter
        //
        DbgPrint(("Regmon: set filter\n"));
        FilterDef = *(PFILTER) InputBuffer;
        RegmonUpdateFilters();
        break;
 
    default:
        DbgPrint (("Regmon: unknown IRP_MJ_DEVICE_CONTROL\n"));
        IoStatus->Status = STATUS_INVALID_DEVICE_REQUEST;
        break;
    }
    return TRUE;
}


//----------------------------------------------------------------------
//
// RegmonDispatch
//
// In this routine we handle requests to our own device. The only 
// requests we care about handling explicitely are IOCTL commands that
// we will get from the GUI. We also expect to get Create and Close 
// commands when the GUI opens and closes communications with us.
//
//----------------------------------------------------------------------
NTSTATUS RegmonDispatch( IN PDEVICE_OBJECT DeviceObject, IN PIRP Irp )
{
    PIO_STACK_LOCATION      irpStack;
    PVOID                   inputBuffer;
    PVOID                   outputBuffer;
    ULONG                   inputBufferLength;
    ULONG                   outputBufferLength;
    ULONG                   ioControlCode;
    PSTORE_BUF              old;
    WORK_QUEUE_ITEM         workItem;

    //
    // Go ahead and set the request up as successful
    //
    Irp->IoStatus.Status      = STATUS_SUCCESS;
    Irp->IoStatus.Information = 0;

    //
    // Get a pointer to the current location in the Irp. This is where
    //     the function codes and parameters are located.
    //
    irpStack = IoGetCurrentIrpStackLocation (Irp);

    //
    // Get the pointer to the input/output buffer and its length
    //
    inputBuffer             = Irp->AssociatedIrp.SystemBuffer;
    inputBufferLength       = irpStack->Parameters.DeviceIoControl.InputBufferLength;
    outputBuffer            = Irp->AssociatedIrp.SystemBuffer;
    outputBufferLength      = irpStack->Parameters.DeviceIoControl.OutputBufferLength;
    ioControlCode           = irpStack->Parameters.DeviceIoControl.IoControlCode;

    switch (irpStack->MajorFunction) {
    case IRP_MJ_CREATE:

        DbgPrint(("Regmon: IRP_MJ_CREATE\n"));

        //
        // Turn off boot logging
        //
        if( BootLogging ) {

            BootLogging = FALSE;
            IoUnregisterShutdownNotification( DeviceObject );
            
            MUTEX_WAIT( StoreMutex );
            
            ExInitializeWorkItem( &workItem, RegmonCloseBootLog, 0 );
            ExQueueWorkItem( &workItem, CriticalWorkQueue );
            KeWaitForSingleObject( &LoggingEvent, Executive, KernelMode, FALSE, NULL );

            MUTEX_RELEASE( StoreMutex ); 
        }

        Sequence = 0;
        GUIActive = TRUE;
        DbgPrint((" GUI Active: %d\n", GUIActive ));
        break;

    case IRP_MJ_SHUTDOWN:
        
        //
        // Dump all accumulated buffers. We are in the system process so
        // there's no need to queue a worker thread item
        //
        while( old = RegmonOldestStore()) {

            RegmonWriteBootLog( old );
            if( old == Store ) break;
        }
        break;

    case IRP_MJ_CLOSE:

        DbgPrint(("Regmon: IRP_MJ_CLOSE\n"));
        GUIActive = FALSE;
        DbgPrint((" GUI closing: %d\n", GUIActive ));
        RegmonResetStore();
        break;
       
    case IRP_MJ_DEVICE_CONTROL:

        DbgPrint (("Regmon: IRP_MJ_DEVICE_CONTROL\n"));

       	//
        // See if the output buffer is really a user buffer that we
        // can just dump data into.
        //
        if( IOCTL_TRANSFER_TYPE(ioControlCode) == METHOD_NEITHER ) {

            outputBuffer = Irp->UserBuffer;
        }

        //
        // Its a request from the GUI
        //
        RegmonDeviceControl( irpStack->FileObject, TRUE,
                             inputBuffer, inputBufferLength, 
                             outputBuffer, outputBufferLength,
                             ioControlCode, &Irp->IoStatus, DeviceObject );
        break;
    }
    IoCompleteRequest( Irp, IO_NO_INCREMENT );
    return STATUS_SUCCESS;   
}


//----------------------------------------------------------------------
//
// RegmonUnload
//
// Our job is done - time to leave.
//
//----------------------------------------------------------------------
VOID RegmonUnload( IN PDRIVER_OBJECT DriverObject )
{
    WCHAR                   deviceLinkBuffer[]  = L"\\DosDevices\\Regmon";
    UNICODE_STRING          deviceLinkUnicodeString;

    DbgPrint(("Regmon.SYS: unloading\n"));

    //
    // Unhook the registry
    //
    if( RegHooked ) UnhookRegistry();

    //
    // Delete the symbolic link for our device
    //
    RtlInitUnicodeString( &deviceLinkUnicodeString, deviceLinkBuffer );
    IoDeleteSymbolicLink( &deviceLinkUnicodeString );

    //
    // Delete the device object
    //
    IoDeleteDevice( DriverObject->DeviceObject );

    DbgPrint(("Regmon.SYS: deleted devices\n"));

    //
    // Now we can free any memory we have outstanding
    //
    RegmonHashCleanup();
    RegmonFreeStore();

    DbgPrint(("Regmon.SYS: freed memory\n"));
}

//----------------------------------------------------------------------
//
// DriverEntry
//
// Installable driver initialization. Here we just set ourselves up.
//
//----------------------------------------------------------------------
NTSTATUS DriverEntry(IN PDRIVER_OBJECT DriverObject, IN PUNICODE_STRING RegistryPath )
{
    NTSTATUS                ntStatus;
    WCHAR                   deviceNameBuffer[]  = L"\\Device\\Regmon";
    UNICODE_STRING          deviceNameUnicodeString;
    WCHAR                   deviceLinkBuffer[]  = L"\\DosDevices\\Regmon";
    UNICODE_STRING          deviceLinkUnicodeString;    
    WCHAR                   startValueBuffer[] = L"Start";
    UNICODE_STRING          startValueUnicodeString;
    WCHAR                   bootMessage[] = 
        L"\nRegmon is logging Registry activity to \\SystemRoot\\Regmon.log\n\n";
    UNICODE_STRING          bootMessageUnicodeString;
    UNICODE_STRING          registryPath; 
    HANDLE                  driverKey;
    PETHREAD                curthread;
    ULONG                   startType, demandStart;
    RTL_QUERY_REGISTRY_TABLE paramTable[2]; 
    OBJECT_ATTRIBUTES       objectAttributes;
    int                     i;

    DbgPrint (("Regmon.SYS: entering DriverEntry\n"));

    // 
    // Query our start type to see if we are supposed to monitor starting
    // at boot time
    //
    registryPath.Buffer = ExAllocatePool( PagedPool, 
                                          RegistryPath->Length + sizeof(UNICODE_NULL)); 
 
    if (!registryPath.Buffer) { 
 
        return STATUS_INSUFFICIENT_RESOURCES; 
    } 
 
    registryPath.Length = RegistryPath->Length + sizeof(UNICODE_NULL); 
    registryPath.MaximumLength = registryPath.Length; 

    RtlZeroMemory( registryPath.Buffer, registryPath.Length ); 
 
    RtlMoveMemory( registryPath.Buffer,  RegistryPath->Buffer, 
                   RegistryPath->Length  ); 

    RtlZeroMemory( &paramTable[0], sizeof(paramTable)); 
    paramTable[0].Flags = RTL_QUERY_REGISTRY_DIRECT; 
    paramTable[0].Name = L"Start"; 
    paramTable[0].EntryContext = &startType;
    paramTable[0].DefaultType = REG_DWORD; 
    paramTable[0].DefaultData = &startType; 
    paramTable[0].DefaultLength = sizeof(ULONG); 

    RtlQueryRegistryValues( RTL_REGISTRY_ABSOLUTE,
                            registryPath.Buffer, &paramTable[0], 
                            NULL, NULL  );

    //
    // Set start type to demand start so that boot logging
    // only happens this boot (unless the user reconfigures it in 
    // the GUI)
    //
    InitializeObjectAttributes( &objectAttributes, RegistryPath,
                                OBJ_CASE_INSENSITIVE, NULL, NULL );
    ntStatus = ZwOpenKey( &driverKey, KEY_WRITE, &objectAttributes );
    if( NT_SUCCESS( ntStatus )) {

        demandStart = SERVICE_DEMAND_START;
        RtlInitUnicodeString( &startValueUnicodeString, startValueBuffer );
        ZwSetValueKey( driverKey, &startValueUnicodeString, 0, REG_DWORD, 
                       &demandStart, sizeof(demandStart ));
        ZwClose( driverKey );
    }

    //
    // Setup our name and symbolic link
    //
    RtlInitUnicodeString (&deviceNameUnicodeString,
                          deviceNameBuffer );
    RtlInitUnicodeString (&deviceLinkUnicodeString,
                          deviceLinkBuffer );

    //
    // Set up the device used for GUI communications
    //
    ntStatus = IoCreateDevice ( DriverObject,
                                0,
                                &deviceNameUnicodeString,
                                FILE_DEVICE_REGMON,
                                0,
                                TRUE,
                                &GUIDevice );
    if (NT_SUCCESS(ntStatus)) {
                
        //
        // Create a symbolic link that the GUI can specify to gain access
        // to this driver/device
        //
        ntStatus = IoCreateSymbolicLink (&deviceLinkUnicodeString,
                                         &deviceNameUnicodeString );

        //
        // Create dispatch points for all routines that must be handled
        //
        DriverObject->MajorFunction[IRP_MJ_SHUTDOWN]        =
        DriverObject->MajorFunction[IRP_MJ_CREATE]          =
        DriverObject->MajorFunction[IRP_MJ_CLOSE]           =
        DriverObject->MajorFunction[IRP_MJ_PNP_POWER]       =
        DriverObject->MajorFunction[IRP_MJ_DEVICE_CONTROL]  = RegmonDispatch;
#if DBG
        DriverObject->DriverUnload                          = RegmonUnload;
#endif
    }
    if (!NT_SUCCESS(ntStatus)) {

        DbgPrint(("Regmon: Failed to create our device!\n"));

        //
        // Something went wrong, so clean up (free resources etc)
        //
        if( GUIDevice ) IoDeleteDevice( GUIDevice );
        IoDeleteSymbolicLink( &deviceLinkUnicodeString );
        return ntStatus;
    }

    //
    // Initialize our mutexes
    //
    MUTEX_INIT( StoreMutex );
    MUTEX_INIT( HashMutex );
    MUTEX_INIT( FilterMutex );

    //
    // Initialize rootkey lengths
    //
    for( i = 0; i < NUMROOTKEYS; i++ )
        RootKey[i].RootNameLen = strlen( RootKey[i].RootName );
    for( i = 0; i < 2; i++ )
        CurrentUser[i].RootNameLen = strlen( CurrentUser[i].RootName );

    //
    // Pointer to system table data structure is an NTOSKRNL export
    //
    ServiceTable = KeServiceDescriptorTable;
    DbgPrint(("Hookregistry: Servicetable: %x\n", ServiceTable ));

    //
    // Find the process name offset
    //
    ProcessNameOffset = GetProcessNameOffset();

    //
    // Allocate the initial output buffer
    //
    Store   = ExAllocatePool( PagedPool, sizeof(*Store) );
    if ( !Store ) {

        IoDeleteDevice( GUIDevice );
        IoDeleteSymbolicLink( &deviceLinkUnicodeString );
        return STATUS_INSUFFICIENT_RESOURCES;
    }
    Store->Len  = 0;
    Store->Next = NULL;
    NumStore = 1;

    //
    // If we're a boot driver start logging now
    //
    if( startType != SERVICE_DEMAND_START ) {

        //
        // Initiate logging
        //
        BootLogging = TRUE;
        
        KeInitializeEvent( &LoggingEvent, SynchronizationEvent, FALSE );
        GUIActive = TRUE;
        
        FilterDef = BootFilter;
        RegmonUpdateFilters();
        HookRegistry();

        //
        // Tell the user that boot-logging is on
        //
        RtlInitUnicodeString( &bootMessageUnicodeString, bootMessage );
        ZwDisplayString( &bootMessageUnicodeString );

        //
        // Register for shutdown notification
        //
        IoRegisterShutdownNotification( GUIDevice );
    }
    return STATUS_SUCCESS;
}

