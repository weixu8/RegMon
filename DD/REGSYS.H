//======================================================================
// 
//  Regmon.h
//
//  Copyright (C) 1996, 1997 Mark Russinovich and Bryce Cogswell
//
//  Typedefs and defines.
// 
//======================================================================

//
// Basic types
//
typedef unsigned int    UINT;
typedef char            CHAR;
typedef char *          PCHAR;
typedef PVOID           POBJECT;

//
// The maximum length of Registry values that will be copied
//
#define MAXVALLEN      256

//
// Maximum seperate filter components 
//
#define MAXFILTERS 64

//
// The maximum registry path length that will be copied
//
#define MAXPATHLEN     1024

//
// Maximum length of data that will be copied to the "other" field in the display
//
#define MAXDATALEN     32

//
// Length of process name buffer. Process names are at most 16 characters so
// we take into account a trailing NULL.
//
#define MAXPROCNAMELEN  20

//
// Maximum length of root keys that we will produce abbreviations for
//
#define MAXROOTLEN      128

//
// Maximum amount of memory that will be grabbed
//
#define MAXMEM          1000000

//
// Invalid handle
//
#define INVALID_HANDLE_VALUE  ((HANDLE) -1)

//
// Convenient mutex macros
//
#define MUTEX_INIT(v)      KeInitializeMutex( &v, 0 )
#define MUTEX_WAIT(v)      KeWaitForMutexObject( &v, Executive, KernelMode, FALSE, NULL )
#define MUTEX_RELEASE(v)   KeReleaseMutex( &v, FALSE )

//
// Definition for system call service table
//
typedef struct _SRVTABLE {
	PVOID           *ServiceTable;
	ULONG           LowCall;        
	ULONG           HiCall;
	PVOID		*ArgTable;
} SRVTABLE, *PSRVTABLE;

//
// Structure for our name hash table
//
typedef struct _nameentry {
   POBJECT              Object;
   PCHAR                FullPathName;
   struct _nameentry    *Next;
} HASH_ENTRY, *PHASH_ENTRY;

//
// Structure for keeping linked lists of output buffers
//
typedef struct _store {
    ULONG               Len;
    struct _store *     Next;
    char                Data[ MAX_STORE ];
} STORE_BUF, *PSTORE_BUF;

//
// Rootkey name translation structure
//
typedef struct _rootkey {
    CHAR                RootName[256];
    CHAR                RootShort[32];
    ULONG               RootNameLen;
} ROOTKEY, *PROOTKEY;

//
// Number of hash buckets
//
#define NUMHASH         0x100
#define HASHOBJECT(_regobject)          (((ULONG)_regobject)>>2)%NUMHASH

//
// Definition for ZwDeleteValueKey call
//
NTSYSAPI
NTSTATUS
NTAPI ZwDeleteValueKey( IN HANDLE, IN PUNICODE_STRING );

//
// Definition for ObQueryNameString call
//
NTSYSAPI
NTSTATUS
NTAPI ObQueryNameString( POBJECT Object, PUNICODE_STRING Name, ULONG MaximumLength, PULONG ActualLength );

//
// For displaying messages to the Blue Screen
//
NTSYSAPI
NTSTATUS
NTAPI ZwDisplayString( PUNICODE_STRING Text );

//
// Undocumented ntoskrnl function for checking user buffer validity
//
VOID NTAPI ProbeForWrite(PVOID Address, 
                         ULONG Length, 
                         ULONG Alignment );


//
// Pointer to the image of the system service table
//
extern PSRVTABLE KeServiceDescriptorTable;


//
// Extract transfer type
//
#define IOCTL_TRANSFER_TYPE( _iocontrol)   (_iocontrol & 0x3)





