/******************************************************************************
*
*       Regmon - Registry Monitor for Windows NT and Windows 9x
*		
*		Copyright (c) 1996 - 1998 Mark Russinovich and Bryce Cogswell
*
*		See readme.txt for terms and conditions.
*
*    	PROGRAM: Regmon.c
*
*    	PURPOSE: Communicates with the RegMon driver to display 
*		registry activity information.
*
******************************************************************************/
#include <windows.h>   
#include <windowsx.h>
#include <tchar.h>
#include <commctrl.h>  
#include <stdio.h>
#include <string.h>
#include <winioctl.h>
#include "resource.h"
#include "ioctlcmd.h"
#include "regmon.h"

// this typedef, present in newer include files,
// supports the building regmon on older systems
typedef struct 
{
    DWORD cbSize;
    DWORD dwMajorVersion;
    DWORD dwMinorVersion;
    DWORD dwBuildNumber;
    DWORD dwPlatformID;
} DLLVERSIONINFO_, *PDLLVERSIONINFO_;

HRESULT (CALLBACK *pDllGetVersionProc)( PDLLVERSIONINFO_ pdvi );

// delay for listview subitem tooltip
#define BALLOONDELAY    10

// toolbar height plus the borders
#define TOOLBARHEIGHT	28

// Number of columns in the listview
#define NUMCOLUMNS	6

// Variables/definitions for the driver that performs the actual monitoring.
#define				SYS_FILE		_T("REGSYS.SYS")
#define				SYS_NAME		_T("REGMON")

#define				VXD_FILE		"\\\\.\\REGVXD.VXD"
#define				VXD_NAME		"REGVXD"

static HANDLE		SysHandle		= INVALID_HANDLE_VALUE;

// length in ms we wait for Regedit to update its display 
#define				REGEDITSLOWWAIT	750

// version number for position settings
#define POSVERSION 400

// Position settings data structure 
typedef struct {
	int		posversion;
	int		left;
	int		top;
	int		width;
	int		height;
	DWORD	column[NUMCOLUMNS];
	DWORD	historydepth;
	BOOLEAN maximized;
	FILTER  filter;
	BOOLEAN	ontop;
} POSITION_SETTINGS;

// The variable that holds the position settings
POSITION_SETTINGS	PositionInfo;

// typedef for balloon popup
typedef struct {
	CHAR	itemText[1024];
	RECT	itemPosition;
} ITEM_CLICK, *PITEM_CLICK;

// toolbar constants
#define ID_TOOLBAR         1

// defined for comtl32.dll version 4.7
#define TOOLBAR_FLAT		0x800

// button definitions

// for installations that support flat style
TBBUTTON tbButtons[] = {
	{ 0, 0, TBSTATE_ENABLED, TBSTYLE_SEP, 0L, 0},
	{ 0, IDM_SAVE, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 8, 0, 0, TBSTYLE_BUTTON, 0L, 0},
	{ 2, IDM_CAPTURE, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 4, IDM_AUTOSCROLL, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 6, IDM_CLEAR, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},	
	{ 8, 0, 0, TBSTYLE_BUTTON, 0L, 0},
	{ 5, IDM_FILTER, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 8, 0, 0, TBSTYLE_BUTTON, 0L, 0},
	{ 7, IDM_FIND, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 9, IDM_JUMP, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 8, 0, 0, TBSTYLE_BUTTON, 0L, 0},
};
#define NUMBUTTONS		12

// for older installations
TBBUTTON tbButtonsOld[] = {
	{ 0, 0, TBSTATE_ENABLED, TBSTYLE_SEP, 0L, 0},
	{ 0, IDM_SAVE, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 0, 0, TBSTATE_ENABLED, TBSTYLE_SEP, 0L, 0},
	{ 2, IDM_CAPTURE, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 4, IDM_AUTOSCROLL, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 6, IDM_CLEAR, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},	
	{ 0, 0, TBSTATE_ENABLED, TBSTYLE_SEP, 0L, 0},
	{ 5, IDM_FILTER, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 0, 0, TBSTATE_ENABLED, TBSTYLE_SEP, 0L, 0},
	{ 7, IDM_FIND, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
	{ 9, IDM_JUMP, TBSTATE_ENABLED, TBSTYLE_BUTTON, 0L, 0},
};						 
#define NUMBUTTONSOLD	11

// Buffer into which driver can copy statistics
char				Stats[ MAX_STORE ];
// Current fraction of buffer filled
DWORD				StatsLen;

// Search string
TCHAR				FindString[256];
FINDREPLACE			FindTextInfo;
DWORD				FindFlags = FR_DOWN;
BOOLEAN				PrevMatch;
TCHAR				PrevMatchString[256];	

// Application instance handle
HINSTANCE			hInst;

// For info saving
TCHAR				szFileName[256];
BOOLEAN				FileChosen = FALSE;

// Windows NT or Windows 9x?
BOOLEAN				IsNT;

// Misc globals
HWND				hWndMain;
HWND				hWndFind = NULL;
UINT				findMessageID;
HWND				hWndList;
WNDPROC 			ListViewWinMain;
HWND				hBalloon = NULL;
BOOLEAN				Capture = TRUE;
BOOLEAN				Autoscroll = TRUE;
BOOLEAN				BootLog = FALSE;
BOOLEAN				BootLogMenuUsed = FALSE;
BOOLEAN				Deleting = FALSE;
BOOLEAN				OnTop = FALSE;

// Driver's registry key
TCHAR				DriverRegistryKey[] = _T("System\\CurrentControlSet\\Services\\Regmon");

// General buffer for storing temporary strings
static TCHAR		msgbuf[ 257 ];

// Filter-related
FILTER				FilterDefinition;

// listview size limiting
DWORD				MaxLines = 0;
DWORD				LastRow = 0;

// General cursor manipulation
HCURSOR 			hSaveCursor;
HCURSOR 			hHourGlass;


/******************************************************************************
*
*	FUNCTION:	RegeditJump
*
*	PURPOSE:	Opens Regedit and navigates the desired key
*
*****************************************************************************/
void RegeditJump( HWND hWnd )
{
	int		currentItem;
	int		pos;
	char	* ch;
	HWND	regeditHwnd, regeditMainHwnd;
	char	compressPath[MAX_PATH];
	HKEY	hKey;
	char	*value = NULL;
	DWORD	status;
	char	RegPath[MAX_PATH];
	DEVMODE	devMode;

	// Get the color depth, which can effect the speed that Regedit
	// responds to keyboard commands
	devMode.dmSize = sizeof(DEVMODE);
	EnumDisplaySettings( NULL, ENUM_CURRENT_SETTINGS, &devMode );

	// See if we can get a Registry path out of the listview
	// find the item with the focus
	currentItem = ListView_GetNextItem( hWndList, -1, LVNI_SELECTED );

	if( currentItem == -1 ) {

		MessageBox( hWnd, _T("No item selected."),
			_T("Regmon"), MB_OK|MB_ICONWARNING );
		return;
	}
	memset( compressPath, 0, MAX_PATH );
	ListView_GetItemText( hWndList, currentItem, 3, compressPath, MAX_PATH );

	// If the key is a handle reference, tell the user we're sorry
	if( compressPath[0] == '0' ) {

		MessageBox( hWnd, _T("The full name of the selected key or value is not available."),
			_T("Regmon"), MB_OK|MB_ICONWARNING );
		return;
	}
	
	// We need to uncompress abbreviations
	if( !strncmp( compressPath, "HKLM", strlen("HKLM"))) {

		sprintf( RegPath, "\\HKEY_LOCAL_MACHINE%s", &compressPath[strlen("HKLM")] );
		status = RegOpenKey( HKEY_LOCAL_MACHINE, &compressPath[strlen("HKLM")+1], &hKey );

	} else if( !strncmp( compressPath, "HKCU", strlen("HKCU"))) {

		sprintf( RegPath, "\\HKEY_CURRENT_USER%s", &compressPath[strlen("HKCU")] );
		status = RegOpenKey( HKEY_CURRENT_USER, &compressPath[strlen("HKCU")+1], &hKey );

	} else if( !strncmp( compressPath, "HKCC", strlen("HKCC"))) {

		sprintf( RegPath, "\\HKEY_CURRENT_CONFIG%s", &compressPath[strlen("HKCC")] );
		status = RegOpenKey( HKEY_CURRENT_CONFIG, &compressPath[strlen("HKCC")+1], &hKey );

	} else if( !strncmp( compressPath, "HKCR", strlen("HKCR"))) {

		sprintf( RegPath, "\\HKEY_CLASSES_ROOT%s", &compressPath[strlen("HKCR")] );
		status = RegOpenKey( HKEY_CLASSES_ROOT, &compressPath[strlen("HKCR")+1], &hKey );

	} else if( !strncmp( compressPath, "HKU", strlen("HKU"))) {

		sprintf( RegPath, "\\HKEY_USERS%s", &compressPath[strlen("HKU")] );
		status = RegOpenKey( HKEY_USERS, &compressPath[strlen("HKU")+1], &hKey );

	} else {

		strcpy( RegPath, compressPath );
		status = FALSE;
	}

	// Is it a value or a key?
	if( status == ERROR_SUCCESS ) {
		
		RegCloseKey( hKey );
		strcat( RegPath, "\\" );

	} else {

		value = strrchr( RegPath, '\\')+1;
		*strrchr( RegPath, '\\' ) = 0;
	}

	// Open RegEdit
	regeditMainHwnd = FindWindow( "RegEdit_RegEdit", NULL );
	if ( regeditMainHwnd == NULL )  {
		SHELLEXECUTEINFO info;
		memset( &info, 0, sizeof info );
		info.cbSize = sizeof info;
		info.fMask	= SEE_MASK_NOCLOSEPROCESS; 
		info.lpVerb	= "open"; 
		info.lpFile	= "regedit.exe"; 
		info.nShow	= SW_SHOWNORMAL; 
		ShellExecuteEx( &info );
		WaitForInputIdle( info.hProcess, INFINITE );
		regeditMainHwnd = FindWindow( "RegEdit_RegEdit", NULL );
	} 

	if( regeditMainHwnd == NULL ) {

		MessageBox( hWnd, _T("Regmon was unable to launch Regedit."),
			_T("Regmon"), MB_OK|MB_ICONERROR );
		return;
	}
    ShowWindow( regeditMainHwnd, SW_SHOW );
	SetForegroundWindow( regeditMainHwnd );

	// Get treeview
	regeditHwnd = FindWindowEx( regeditMainHwnd, NULL, "SysTreeView32", NULL );
	SetForegroundWindow( regeditHwnd );
	SetFocus( regeditHwnd );

	// Close it up
	for ( pos = 0; pos < 30; ++pos )  {
		UINT vk = VK_LEFT;
		SendMessage( regeditHwnd, WM_KEYDOWN, vk, 0 );
	}

	// wait for slow displays - 
	// Regedit takes a while to open keys with lots of subkeys
	// when running at high color depths 
	if( devMode.dmBitsPerPel > 8 ) Sleep(REGEDITSLOWWAIT); 

	// Open path
	for ( ch = RegPath; *ch; ++ch )  {
		if ( *ch == '\\' )  {
			UINT vk = VK_RIGHT;
			SendMessage( regeditHwnd, WM_KEYDOWN, vk, 0 );

			// wait for slow displays - 
			// Regedit takes a while to open keys with lots of subkeys
			// when running at high color depths 
			if( devMode.dmBitsPerPel > 8 ) Sleep(REGEDITSLOWWAIT); 

		} else {
			UINT vk = toupper(*ch);

			SendMessage( regeditHwnd, WM_CHAR, vk, 0 );
		}
	}

	// If its a value select the value
	if( value ) {
		UINT vk = VK_HOME;

		regeditHwnd = FindWindowEx( regeditMainHwnd, NULL, "SysListView32", NULL );
		SetForegroundWindow( regeditHwnd );
		SetFocus( regeditHwnd );
		Sleep(1000); // have to wait for Regedit to update listview
		SendMessage( regeditHwnd, WM_KEYDOWN, vk, 0 );

		for ( ch = value; *ch; ++ch )  {
			UINT vk = toupper(*ch);

			SendMessage( regeditHwnd, WM_CHAR, vk, 0 );
		}
	}

	SetForegroundWindow( regeditMainHwnd );
	SetFocus( regeditMainHwnd );
}

/******************************************************************************
*
*	FUNCTION:	Abort:
*
*	PURPOSE:	Handles emergency exit conditions.
*
*****************************************************************************/
LONG Abort( HWND hWnd, TCHAR * Msg )
{
	LPVOID	lpMsgBuf;
	TCHAR	errmsg[256];
	DWORD	error = GetLastError();
 
	FormatMessage( FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM,
					NULL, GetLastError(), 
					MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),
					(LPTSTR) &lpMsgBuf, 0, NULL );
	if( IsNT ) UnloadDeviceDriver( SYS_NAME );
	sprintf(errmsg, _T("%s: %s"), Msg, lpMsgBuf );
	if( error == ERROR_INVALID_HANDLE && IsNT ) 
		wsprintf(errmsg, _T("%s\nMake sure that you are an administrator and that ")
			_T("Regmon is located on a local drive."), errmsg  );
	MessageBox( hWnd, errmsg, _T("Regmon"), MB_OK|MB_ICONERROR );
	PostQuitMessage( 1 );
	LocalFree( lpMsgBuf );
	return -1;
}

/******************************************************************************
*
*	FUNCTION:	BalloonDialog
*
*	PURPOSE:	Dialog function for home-brewed balloon help.
*
******************************************************************************/
LONG APIENTRY BalloonDialog( HWND hDlg, UINT message, UINT wParam, LONG lParam )
{
	static ITEM_CLICK	ctx;
	static RECT			rect;
	static HFONT		hfont;
	LPCREATESTRUCT		lpcs;
	HDC					hdc;
	POINTS				pts;
	POINT				pt;
	DWORD				newclicktime;
    NONCLIENTMETRICS	ncm;
	static POINT		lastclickpt = {0,0};
	static DWORD		lastclicktime = 0;	

	switch (message) {
		case WM_CREATE:

			lpcs = (void *)lParam;
			ctx = *(PITEM_CLICK) lpcs->lpCreateParams;
			hdc = GetDC( hDlg );

			// Get font
			if ( hfont == NULL )  {

				memset(&ncm, 0, sizeof(ncm));
				ncm.cbSize = sizeof(ncm);
				SystemParametersInfo( SPI_GETNONCLIENTMETRICS, 
										0, &ncm, 0);
 				hfont = CreateFontIndirect( &ncm.lfMessageFont ); 
			} 

			// is the app the focus?
			if( !GetFocus()) return -1;

			// Compute size of required rectangle
			rect.left	= 0;
			rect.top	= 0;
			rect.right	= lpcs->cx;
			rect.bottom	= lpcs->cy;
			SelectObject( hdc, hfont );
			DrawText( hdc, ctx.itemText, -1, &rect, 
						DT_NOCLIP|DT_LEFT|DT_NOPREFIX|DT_CALCRECT );

			// if the bounding rectangle of the subitem is big enough to display
			// the text then don't pop the balloon
			if( ctx.itemPosition.right > rect.right + 11 ) {

				return -1;
			}

			// Move and resize window
			if( ctx.itemPosition.left - 5 + rect.right + 10 >
				 GetSystemMetrics(SM_CXFULLSCREEN) ) {

				 ctx.itemPosition.left = GetSystemMetrics(SM_CXFULLSCREEN) -
							(rect.right+10);
			}
			MoveWindow( hDlg, 
						ctx.itemPosition.left+3, ctx.itemPosition.top, 
						rect.right + 6, 
						rect.bottom + 1,
						TRUE );

			// Adjust rectangle so text is centered
			rect.left	+= 2;
			rect.right	+= 2;
			rect.top	-= 1; 
			rect.bottom	+= 0;

			// make it so this window doesn't get the focus
			ShowWindow( hDlg, SW_SHOWNOACTIVATE );
			break;

		case WM_LBUTTONDBLCLK:
		case WM_RBUTTONDBLCLK:
		case WM_MBUTTONDBLCLK:
		case WM_LBUTTONDOWN:
		case WM_RBUTTONDOWN:
		case WM_MBUTTONDOWN:
		case WM_LBUTTONUP:
		case WM_RBUTTONUP:
		case WM_MBUTTONUP:

			pts = MAKEPOINTS( lParam );
			pt.x = (LONG) pts.x;
			pt.y = (LONG) pts.y;
			ClientToScreen( hDlg, &pt );

			// pass this through to the listview
			if( ScreenToClient( hWndList, &pt )) {

				if( message == WM_LBUTTONDOWN ) {

					// see if its a double click
					newclicktime = GetTickCount();
					if( pt.x == lastclickpt.x && pt.y == lastclickpt.y && 
						newclicktime - lastclicktime < 300 ) {

						message = WM_LBUTTONDBLCLK;
					}
					lastclicktime = newclicktime;
					lastclickpt = pt;
				}

				PostMessage( hWndList, message, wParam, (SHORT) pt.y<<16 | (SHORT) pt.x );
			}
			break;

		case WM_PAINT:
			hdc = GetDC( hDlg );

			// Set colors
			SetTextColor( hdc, 0x00000000 );
			SetBkMode( hdc, TRANSPARENT );
			SelectObject( hdc, hfont );
			DrawText( hdc, ctx.itemText, -1, &rect, 
						DT_NOCLIP|DT_LEFT|DT_NOPREFIX|DT_WORDBREAK );
			break;

		case WM_DESTROY:
			hBalloon = NULL;
			break;

		case WM_CLOSE:	
			DestroyWindow( hDlg );
			break;
	}

    return DefWindowProc( hDlg, message, wParam, lParam );
}


/******************************************************************************
*
*	FUNCTION:	FindInListview:
*
*	PURPOSE:	Searches for a string in the listview. Note: its okay if
*				items are being added to the list view or the list view
*				is cleared while this search is in progress - the effect
*				is harmless.
*
*****************************************************************************/
BOOLEAN FindInListview(HWND hWnd, LPFINDREPLACE FindInfo )
{
	int		currentItem;
	DWORD	i;
	int		subitem, numItems;
	TCHAR	fieldtext[256];
	BOOLEAN match = FALSE;
	TCHAR	errmsg[256];
	BOOLEAN	goUp;

	// get the search direction
	goUp = ((FindInfo->Flags & FR_DOWN) == FR_DOWN);

	// initialize stuff
	if( !(numItems = ListView_GetItemCount( hWndList ))) {

		MessageBox( hWnd, _T("No items to search"), _T("Regmon"), 
			MB_OK|MB_ICONWARNING );
		SetForegroundWindow( hWndFind );
		return FALSE;
	}

	// find the item with the focus
	currentItem = ListView_GetNextItem( hWndList, 0, LVNI_SELECTED );

	// if no current item, start at the top or the bottom
	if( currentItem == -1 ) {
		if( goUp )
			currentItem = 0;
		else {
			if( PrevMatch ) {
				sprintf(errmsg, _T("Cannot find string \"%s\""), FindInfo->lpstrFindWhat );
				MessageBox( hWnd, errmsg, _T("Regmon"), MB_OK|MB_ICONWARNING );
				SetForegroundWindow( hWndFind );
				return FALSE;
			}
			currentItem = numItems;
		}
	}

	// if we're continuing a search, start with the next item
	if( PrevMatch && !strcmp( FindString, PrevMatchString ) ) {
		if( goUp ) currentItem++;
		else currentItem--;

		if( (!goUp && currentItem < 0) ||
			(goUp && currentItem >= numItems )) {

			sprintf(errmsg, _T("Cannot find string \"%s\""), FindInfo->lpstrFindWhat );
			MessageBox( hWnd, errmsg, _T("Regmon"), MB_OK|MB_ICONWARNING );
			SetForegroundWindow( hWndFind );
			return FALSE;
		}
	}

	// loop through each item looking for the string
	while( 1 ) {

		// get the item text
		for( subitem = 0; subitem < NUMCOLUMNS; subitem++ ) {
			fieldtext[0] = 0;
			ListView_GetItemText( hWndList, currentItem, subitem, fieldtext, MAX_PATH );

			// make sure enought string for a match
			if( strlen( fieldtext ) < strlen( FindInfo->lpstrFindWhat ))
				continue;

			// do a scan all the way through for the substring
			if( FindInfo->Flags & FR_WHOLEWORD ) {

				i = 0;
				while( fieldtext[i] ) {
					while( fieldtext[i] && fieldtext[i] != ' ' ) i++;
					if( FindInfo->Flags & FR_MATCHCASE ) 
						match = !strcmp( fieldtext, FindInfo->lpstrFindWhat );
					else
						match = !stricmp( fieldtext, FindInfo->lpstrFindWhat );
					if( match) break;
					i++;
				}	
			} else {
				for( i = 0; i < strlen( fieldtext ) - strlen(FindInfo->lpstrFindWhat)+1; i++ ) {
					if( FindInfo->Flags & FR_MATCHCASE ) 
						match = !strncmp( &fieldtext[i], FindInfo->lpstrFindWhat, 
											strlen(FindInfo->lpstrFindWhat) );
					else
						match = !strnicmp( &fieldtext[i], FindInfo->lpstrFindWhat,
											strlen(FindInfo->lpstrFindWhat) );
					if( match ) break;
				}		
			}

			if( match ) {

				strcpy( PrevMatchString, FindInfo->lpstrFindWhat );
				PrevMatch = TRUE;
				ListView_SetItemState( hWndList, currentItem, 
							LVIS_SELECTED|LVIS_FOCUSED,
							LVIS_SELECTED|LVIS_FOCUSED );
				ListView_EnsureVisible( hWndList, currentItem, FALSE ); 
				SetFocus( hWndList );
				return TRUE;
			}
		}
		currentItem = currentItem + (goUp ? 1:-1);
		if( !currentItem || currentItem == numItems+1 ) {
			// end of the road
			break;
		}
	}
	sprintf(errmsg, _T("Cannot find string \"%s\""), FindInfo->lpstrFindWhat );
	MessageBox( hWnd, errmsg, _T("Regmon"), MB_OK|MB_ICONWARNING );
	SetForegroundWindow( hWndFind );
	return FALSE;
}


/******************************************************************************
*
*	FUNCTION:	PopFindDialog:
*
*	PURPOSE:	Calls the find message dialog box.
*
*****************************************************************************/
void PopFindDialog(HWND hWnd)
{
	strcpy( FindString, PrevMatchString );
    FindTextInfo.lStructSize = sizeof( FindTextInfo );
    FindTextInfo.hwndOwner = hWnd;
    FindTextInfo.hInstance = (HANDLE)hInst;
    FindTextInfo.lpstrFindWhat = FindString;
    FindTextInfo.lpstrReplaceWith = NULL;
    FindTextInfo.wFindWhatLen = sizeof(FindString);
    FindTextInfo.wReplaceWithLen = 0;
    FindTextInfo.lCustData = 0;
    FindTextInfo.Flags =  FindFlags;
    FindTextInfo.lpfnHook = (LPFRHOOKPROC)(FARPROC)NULL;
    FindTextInfo.lpTemplateName = NULL;

    if ((hWndFind = FindText(&FindTextInfo)) == NULL)
		MessageBox( hWnd, _T("Unable to create Find dialog"), _T("Regmon"), MB_OK|MB_ICONERROR );      
}


/******************************************************************************
*
*	FUNCTION:	Get_Position_Settings
*
*	PURPOSE:	Reads the Registry to get the last-set window position.
*
******************************************************************************/
VOID Get_Position_Settings()
{
	HKEY	hKey;
	DWORD	ParamSize;
	POSITION_SETTINGS	regPositionInfo;

	// Fist, set the default settings
	PositionInfo.top	= CW_USEDEFAULT;
	PositionInfo.left	= CW_USEDEFAULT;
	PositionInfo.width	= CW_USEDEFAULT;
	PositionInfo.height	= CW_USEDEFAULT;
	PositionInfo.maximized = FALSE;
	PositionInfo.ontop = FALSE;

	// set the default listview widths
	PositionInfo.column[0] = 35;
	PositionInfo.column[1] = 90;
	PositionInfo.column[2] = 130;
	PositionInfo.column[3] = 200;
	PositionInfo.column[4] = 70;
	PositionInfo.column[5] = 150;

	// Initialize the filter
	sprintf( PositionInfo.filter.processfilter, "*" );
	strcpy( PositionInfo.filter.processexclude, "" );
	sprintf( PositionInfo.filter.pathfilter,    "*" );
	sprintf( PositionInfo.filter.excludefilter, "" );
	PositionInfo.filter.logsuccess = TRUE;
	PositionInfo.filter.logerror   = TRUE;
	PositionInfo.filter.logreads   = TRUE;
	PositionInfo.filter.logwrites  = TRUE;

	// set the default history depth (infinite)
	PositionInfo.historydepth = 0;

	// first, get the last-entered params from the registry
	RegCreateKey(HKEY_CURRENT_USER, 
			_T("Software\\Systems Internals\\Regmon"),
			&hKey );

	// get the params and ignore errors
	ParamSize = sizeof( PositionInfo );
	regPositionInfo.posversion = 0;
	RegQueryValueEx( hKey,_T("Settings"), NULL, NULL, (LPBYTE) &regPositionInfo,
				&ParamSize );
	RegCloseKey( hKey );

	// only use the registry settings if the version matches
	if( regPositionInfo.posversion == POSVERSION ) PositionInfo = regPositionInfo;

	// extract the history depth
	MaxLines			= PositionInfo.historydepth;
	OnTop				= PositionInfo.ontop;

	// initialize filter
	FilterDefinition    = PositionInfo.filter;
}


/******************************************************************************
*
*	FUNCTION:	Save_Position_Settings
*
*	PURPOSE:	Saves the current window settings to the Registry.
*
******************************************************************************/
VOID Save_Position_Settings( HWND hWnd )
{
	RECT		rc;
	int			i;
	HKEY		hKey;

	// set version #
	PositionInfo.posversion = POSVERSION;

	// get the position of the main window
	GetWindowRect( hWnd, &rc );
	if( !IsIconic( hWnd )) {

		PositionInfo.left = rc.left;
		PositionInfo.top = rc.top;
		PositionInfo.width = rc.right - rc.left;
		PositionInfo.height = rc.bottom - rc.top;
	} 
	PositionInfo.maximized = IsZoomed( hWnd );
	PositionInfo.ontop = OnTop;

	// get the widths of the listview columns
	for( i = 0; i < NUMCOLUMNS; i++ ) {
		PositionInfo.column[i] = ListView_GetColumnWidth( hWndList, i );
	}

	// get the history depth
	PositionInfo.historydepth = MaxLines;

	// save filters
	PositionInfo.filter = FilterDefinition;

	// save connection info to registry
	RegOpenKey(HKEY_CURRENT_USER, 
			_T("Software\\Systems Internals\\Regmon"),
			&hKey );
	RegSetValueEx( hKey, _T("Settings"), 0, REG_BINARY, (LPBYTE) &PositionInfo,
			sizeof( PositionInfo ) );
	RegCloseKey( hKey );
}	


/******************************************************************************
*
*	FUNCTION:	Split
*
*	PURPOSE:	Split a delimited line into components
*
******************************************************************************/
int Split( char * line, char delimiter, char * items[] )
{
	int		cnt = 0;

	for (;;)  {
		// Add prefix to list of components		
		items[cnt++] = line;

		// Check for more components
		line = strchr( line, delimiter );
		if ( line == NULL )
			return cnt;

		// Terminate previous component and move to next
		*line++ = '\0';
	}		
}


/******************************************************************************
*
*	FUNCTION:	ListAppend
*
*	PURPOSE:	Add a new line to List window
*
******************************************************************************/
BOOL List_Append( HWND hWndList, DWORD seq, char * line )
{
	LV_ITEM		lvI;	// list view item structure
	int			row;
	char	*	items[20];
	int			itemcnt = 0;

	// Split line into columns
	itemcnt = Split( line, '\t', items );
	if ( itemcnt == 0 )
		return FALSE;

	// Determine row number for request
	if ( *items[0] )  {
		// Its a new request.  Put at end.
		row = 0x7FFFFFFF;
	} else {
		// Its a status.  Locate its associated request.
		lvI.mask = LVIF_PARAM;
		lvI.iSubItem = 0;
		for ( row = ListView_GetItemCount(hWndList) - 1; row >= 0; --row )  {
			lvI.iItem = row;
			if ( ListView_GetItem( hWndList, &lvI )  &&  (DWORD)lvI.lParam == seq )
				break;
		}
		if ( row == -1 )
			// No request associated with status.
			return FALSE;
	}

	// Sequence number if a new item
	if ( *items[0] )  {
		wsprintf( msgbuf, _T("%d"), seq );
		lvI.mask		= LVIF_TEXT | LVIF_PARAM;
		lvI.iItem		= row;
		lvI.iSubItem	= 0;
		lvI.pszText		= msgbuf;
		lvI.cchTextMax	= lstrlen( lvI.pszText ) + 1;
		lvI.lParam		= seq;
		row = ListView_InsertItem( hWndList, &lvI );
		if ( row == -1 )  {
			wsprintf( msgbuf, _T("Error adding item %d to list view"), seq );
			MessageBox( hWndList, msgbuf, _T("Regmon Error"), MB_OK );
			return FALSE;
		}
        LastRow = row;
	}

	// Process name
	if ( itemcnt>0 && *items[0] ) {
		OemToChar( items[0], msgbuf );
		ListView_SetItemText( hWndList, row, 1, msgbuf );
	}

	// Request type
	if ( itemcnt>1 && *items[1] )  {
		OemToChar( items[1], msgbuf );
		ListView_SetItemText( hWndList, row, 2, msgbuf );
	}

	// Path
	if ( itemcnt>2 && *items[2] )  {
		OemToChar( items[2], msgbuf );
		ListView_SetItemText( hWndList, row, 3, msgbuf );
	}

	// Result
	if ( itemcnt>3 && *items[3] )  {
		OemToChar( items[3], msgbuf );
		ListView_SetItemText( hWndList, row, 4, msgbuf );
	}

	// Additional
	if ( itemcnt>4 && *items[4] )  {
		OemToChar( items[4], msgbuf );
		ListView_SetItemText( hWndList, row, 5, msgbuf );
	}

	return TRUE;
}


/******************************************************************************
*
*	FUNCTION:	UpdateStatistics
*
*	PURPOSE:	Clear the statistics window and refill it with the current 
*				contents of the statistics buffer.  Does not refresh the 
*				buffer from the device driver.
*
******************************************************************************/
void UpdateStatistics( HWND hWnd, HWND hWndList, BOOL Clear )
{
	PENTRY	ptr;
	BOOLEAN itemsAdded = FALSE;
	int		totitems, i;

	// Just return if nothing to do
	if ( !Clear  &&  StatsLen < sizeof(int)+2 )
		return;

	if( !IsNT ) {
		
		hSaveCursor = SetCursor(hHourGlass);
		SendMessage(hWndList, WM_SETREDRAW, FALSE, 0);
	}

	// Start with empty list
	if ( Clear ) {

		if( IsNT ) {

			ListView_DeleteAllItems( hWndList );
		} else {

			totitems = ListView_GetItemCount( hWndList );
			Deleting = TRUE;
			for(i = 0; i < totitems; i++)
				ListView_DeleteItem( hWndList, 0 );
			Deleting = FALSE;
		}
		LastRow = 0;
	}

	// Add all List items from Stats[] data
	for ( ptr = (void *)Stats; (char *)ptr < min(Stats+StatsLen,Stats + sizeof (Stats)); )  {
	 	// Add to list
		ULONG len = strlen(ptr->text);
        if( IsNT ) {
			
			len += 4; len &= 0xFFFFFFFC; // +1 for null-terminator +3 for 32bit alignment
		}

		itemsAdded |= List_Append( hWndList, ptr->seq, ptr->text );
		
		if( IsNT ) ptr = (void *)(ptr->text + len);
		else       ptr = (void *)(ptr->text + len + 1);
	}

	// Empty the buffer
	StatsLen = 0;

	// only do this if we added items
	if( itemsAdded ) {

		// limit number of lines saved
		if (MaxLines) {
			SendMessage(hWndList, WM_SETREDRAW, FALSE, 0);
			while ( LastRow > MaxLines ) {
				ListView_DeleteItem ( hWndList, 0 );
				LastRow--;
			}
			SendMessage(hWndList, WM_SETREDRAW, TRUE, 0);
		}

		// Scroll so newly added items are visible
		if ( Autoscroll ) {
			if( hBalloon ) DestroyWindow( hBalloon );
			ListView_EnsureVisible( hWndList, ListView_GetItemCount(hWndList)-1, FALSE ); 
		}
	}

	if( !IsNT ) {
		SetCursor( hSaveCursor );
		SendMessage(hWndList, WM_SETREDRAW, TRUE, 0);
		InvalidateRect( hWndList, NULL, FALSE );
	}
}


/****************************************************************************
* 
*    FUNCTION: ListViewSubclass(HWND,UINT,WPARAM)
*
*    PURPOSE:  Subclasses the listview so that we can do tooltips
*
****************************************************************************/
LRESULT CALLBACK ListViewSubclass(HWND hWnd, UINT uMsg, WPARAM wParam,
        LPARAM lParam)
{
	ITEM_CLICK		itemClick;
	LVHITTESTINFO	hitItem;
	static initTrack = FALSE;
	POINT           hitPoint, topleftPoint, bottomrightPoint;
	RECT			listRect;
	static POINTS  mousePosition;

	if( !initTrack ) {

		SetTimer( hWnd,	2, BALLOONDELAY, NULL );
		initTrack = TRUE;
	}

    switch (uMsg) {

	case WM_LBUTTONDBLCLK:
	case WM_RBUTTONDBLCLK:
	case WM_MBUTTONDBLCLK:
	case WM_LBUTTONUP:
	case WM_RBUTTONUP:
	case WM_MBUTTONUP:
	case WM_LBUTTONDOWN:
	case WM_MBUTTONDOWN:
	case WM_MOUSEMOVE:
		// delete any existing balloon
		if( hBalloon ) DestroyWindow( hBalloon );

		// save mouse position and reset the timer
		mousePosition = MAKEPOINTS( lParam );
		SetTimer( hWnd,	2, BALLOONDELAY, NULL );
		break;

	case WM_KEYDOWN:
	case WM_VSCROLL:
	case WM_HSCROLL:
		if( hBalloon ) DestroyWindow( hBalloon );
		break;

	case WM_RBUTTONDOWN:
		mousePosition = MAKEPOINTS( lParam );
		SetTimer( hWnd,	2, BALLOONDELAY, NULL );
		// fall-through

	case WM_TIMER:

		// are we currently in the listview?
		GetCursorPos( &hitPoint );
		GetClientRect( hWnd, &listRect );
		topleftPoint.x = listRect.left;
		topleftPoint.y = listRect.top;
		ClientToScreen( hWnd, &topleftPoint );
		bottomrightPoint.x = listRect.right;
		bottomrightPoint.y = listRect.bottom;
		ClientToScreen( hWnd, &bottomrightPoint );
		if( hitPoint.x < topleftPoint.x ||
			hitPoint.x > bottomrightPoint.x ||
			hitPoint.y < topleftPoint.y ||
			hitPoint.y > bottomrightPoint.y ||
			(hWndFind && GetFocus() != hWndList) ) {

			// delete any existing balloon
			if( hBalloon ) DestroyWindow( hBalloon );
			break;
		}

		hitItem.pt.x = mousePosition.x;
		hitItem.pt.y =  mousePosition.y;
		if(	ListView_SubItemHitTest( hWndList, &hitItem ) != -1 ) {

			itemClick.itemText[0] = 0;
			ListView_GetItemText( hWndList, hitItem.iItem,
					hitItem.iSubItem, itemClick.itemText, 1024 );

			// delete any existing balloon
			if( hBalloon ) DestroyWindow( hBalloon );

			if( strlen( itemClick.itemText ) ) {

				if( hitItem.iSubItem ) {

					ListView_GetSubItemRect( hWndList, hitItem.iItem, hitItem.iSubItem,
							LVIR_BOUNDS, &itemClick.itemPosition);

					itemClick.itemPosition.bottom -= itemClick.itemPosition.top;
					itemClick.itemPosition.right  -= itemClick.itemPosition.left;

				} else {

					ListView_GetSubItemRect( hWndList, hitItem.iItem, 1,
							LVIR_BOUNDS, &itemClick.itemPosition);

					itemClick.itemPosition.bottom -= itemClick.itemPosition.top;
					itemClick.itemPosition.right  = itemClick.itemPosition.left;
					itemClick.itemPosition.left   = 0;
				}

				hitPoint.y = itemClick.itemPosition.top;
				hitPoint.x = itemClick.itemPosition.left;

				ClientToScreen( hWnd, &hitPoint );

				itemClick.itemPosition.left = hitPoint.x;
				itemClick.itemPosition.top  = hitPoint.y;

				// pop-up a balloon (tool-tip like window)
				hBalloon = CreateWindowEx( 0, _T("BALLOON"), 
								_T("balloon"), 
								WS_POPUP|WS_BORDER,
								100, 100,
								200, 200,
								hWndMain, NULL, hInst, 
								&itemClick );
				if( hBalloon) SetFocus( hWnd );
			}
		}
		break;
    }

	// pass-through to real listview handler
    return CallWindowProc(ListViewWinMain, hWnd, uMsg, wParam, 
            lParam);
}


/****************************************************************************
* 
*    FUNCTION: CreateListView(HWND)
*
*    PURPOSE:  Creates the statistics list view window and initializes it
*
****************************************************************************/
HWND CreateList( HWND hWndParent )                                     
{
	HWND		hWndList;    	  	// handle to list view window
	RECT		rc;         	  	// rectangle for setting size of window
	LV_COLUMN	lvC;				// list view column structure
	DWORD		j;
	static struct {
		TCHAR *	Label;	// title of column
		DWORD	Width;	// width of column in pixels
		DWORD	Fmt;
	} column[] = {
		{	"#"			,	35		},
		{	"Process"	,	90		},
		{	"Request"	,	90		},
		{	"Path"		,	225		},
		{	"Result"	,	90		},
		{	"Other"		,	150		},
	};

	// Ensure that the common control DLL is loaded.
	InitCommonControls();

	// Set the column widths according to the user-settings
	for( j = 0; j < NUMCOLUMNS; j++ ) {
		column[j].Width = PositionInfo.column[j];
	}

	// Get the size and position of the parent window.
	GetClientRect( hWndParent, &rc );

	// Create the list view window
	hWndList = CreateWindowEx( /* WS_EX_CLIENTEDGE */ 0L, WC_LISTVIEW, _T(""), 
								WS_VISIBLE | WS_CHILD | WS_BORDER | LVS_REPORT |
								LVS_SINGLESEL,
								0, TOOLBARHEIGHT, rc.right - rc.left, rc.bottom - rc.top - TOOLBARHEIGHT,
								hWndParent,	(HMENU)ID_LIST, hInst, NULL );
	if ( hWndList == NULL )
		return NULL;

	// Initialize columns
	lvC.mask	= LVCF_FMT | LVCF_WIDTH | LVCF_TEXT | LVCF_SUBITEM;
	lvC.fmt		= LVCFMT_LEFT;	// left-align column

	// Add the columns.
	for ( j = 0; j < sizeof column/sizeof column[0]; ++j )  {
		lvC.iSubItem	= j;
		lvC.cx			= column[j].Width;
	 	lvC.pszText		= column[j].Label;
		if ( ListView_InsertColumn( hWndList, j, &lvC ) == -1 )
			return NULL;
	}

	// set full-row selection
	SendMessage( hWndList, LVM_SETEXTENDEDLISTVIEWSTYLE,
			LVS_EX_FULLROWSELECT, LVS_EX_FULLROWSELECT );

	// sub-class
	ListViewWinMain = (WNDPROC) SetWindowLong(hWndList, 
                                              GWL_WNDPROC, 
                                              (DWORD)ListViewSubclass); 
	return hWndList;
}


/****************************************************************************
* 
*    FUNCTION: SaveFile()
*
*    PURPOSE:  Lets the user go select a file.
*
****************************************************************************/
void SaveFile( HWND hWnd, HWND ListBox, BOOLEAN SaveAs )
{
	OPENFILENAME	SaveFileName;
	char			szFile[256] = "", fieldtext[256], output[1024];
	FILE			*hFile;
	int				numitems;
	int				row, subitem;

	if( SaveAs || !FileChosen ) {
		SaveFileName.lStructSize       = sizeof (SaveFileName);
		SaveFileName.hwndOwner         = hWnd;
		SaveFileName.hInstance         = (HANDLE) hInst;
		SaveFileName.lpstrFilter       = "Reg Data (*.RGD)\0*.RGD\0All (*.*)\0*.*\0";
		SaveFileName.lpstrCustomFilter = (LPTSTR)NULL;
		SaveFileName.nMaxCustFilter    = 0L;
		SaveFileName.nFilterIndex      = 1L;
		SaveFileName.lpstrFile         = szFile;
		SaveFileName.nMaxFile          = 256;
		SaveFileName.lpstrFileTitle    = NULL;
		SaveFileName.nMaxFileTitle     = 0;
		SaveFileName.lpstrInitialDir   = NULL;
		SaveFileName.lpstrTitle        = "Save File Info...";
		SaveFileName.nFileOffset       = 0;
		SaveFileName.nFileExtension    = 0;
		SaveFileName.lpstrDefExt       = "*.rgd";
		SaveFileName.lpfnHook		   = NULL;
 		SaveFileName.Flags = OFN_LONGNAMES|OFN_HIDEREADONLY;

		if( !GetSaveFileName( &SaveFileName )) 
			return;
	} else 
		// open previous szFile
		strcpy( szFile, szFileName );

	// open the file
	hFile = fopen( szFile, "w" );
	if( !hFile ) {
		MessageBox(	NULL, "Create File Failed.",
				"Save Error", MB_OK|MB_ICONSTOP );
		return;
	}
	// post hourglass icon
	SetCapture(hWnd);
	hSaveCursor = SetCursor(hHourGlass);

	numitems = ListView_GetItemCount(ListBox);
	for ( row = 0; row < numitems; row++ )  {
		output[0] = 0;
		for( subitem = 0; subitem < 6; subitem++ ) {
			fieldtext[0] = 0;
			ListView_GetItemText( ListBox, row, subitem, fieldtext, 256 );
			strcat( output, fieldtext );
			strcat( output, "\t" );
		}
		fprintf( hFile, "%s\n", output );
	}
	fclose( hFile );
	strcpy( szFileName, szFile );
	FileChosen = TRUE;
	SetCursor( hSaveCursor );
	ReleaseCapture(); 
}



/****************************************************************************
*
*	FUNCTION:	FilterProc
*
*	PURPOSE:	Processes messages for "Filter" dialog box
*
****************************************************************************/
BOOL APIENTRY FilterProc( HWND hDlg, UINT message, UINT wParam, LONG lParam )
{
	int				nb;
	FILTER			upcaseFilter;
	DWORD			newMaxLines;
	char			history[64];

	switch ( message )  {
	case WM_INITDIALOG:

		// initialize the controls to reflect the current filter
		SetDlgItemText( hDlg, IDC_PROCFILTER, FilterDefinition.processfilter );
		SetDlgItemText( hDlg, IDC_PROCEXCLUDE, FilterDefinition.processexclude );
		SetDlgItemText( hDlg, IDC_PATHFILTER, FilterDefinition.pathfilter );
		SetDlgItemText( hDlg, IDC_EXCLUDEFILTER, FilterDefinition.excludefilter );
		CheckDlgButton( hDlg, IDC_SUCCESS, FilterDefinition.logsuccess );
		CheckDlgButton( hDlg, IDC_ERROR,   FilterDefinition.logerror );
		CheckDlgButton( hDlg, IDC_LOGREADS, FilterDefinition.logreads );
		CheckDlgButton( hDlg, IDC_LOGWRITES,   FilterDefinition.logwrites );
		sprintf( history, "%d", MaxLines );
		SetDlgItemText( hDlg, IDC_HISTORY, history );
		return TRUE;

	case WM_COMMAND:              
		if ( LOWORD( wParam ) == IDOK )	 {

			// make sure that max lines is legal
			GetDlgItemTextA( hDlg, IDC_HISTORY, history, 64 );
			if( !sscanf( history, "%d", &newMaxLines )) {

				MessageBox(	NULL, _T("Invalid History Depth."),
						_T("Filter Error"), MB_OK|MB_ICONWARNING );
				return TRUE;
			} 
			MaxLines = newMaxLines;

			// read the values that were set
			GetDlgItemText( hDlg, IDC_PROCFILTER, FilterDefinition.processfilter, MAXFILTERLEN );
			GetDlgItemText( hDlg, IDC_PROCEXCLUDE, FilterDefinition.processexclude, MAXFILTERLEN );
			GetDlgItemText( hDlg, IDC_PATHFILTER, FilterDefinition.pathfilter, MAXFILTERLEN );
			GetDlgItemText( hDlg, IDC_EXCLUDEFILTER, FilterDefinition.excludefilter, MAXFILTERLEN );
			FilterDefinition.logsuccess = IsDlgButtonChecked( hDlg, IDC_SUCCESS );
			FilterDefinition.logerror   = IsDlgButtonChecked( hDlg, IDC_ERROR );
			FilterDefinition.logreads = IsDlgButtonChecked( hDlg, IDC_LOGREADS );
			FilterDefinition.logwrites   = IsDlgButtonChecked( hDlg, IDC_LOGWRITES );

			// make an upcase version for the driver
			upcaseFilter = FilterDefinition;
			_strupr(upcaseFilter.processfilter);
			_strupr(upcaseFilter.processexclude);
			_strupr(upcaseFilter.pathfilter);
			_strupr(upcaseFilter.excludefilter);
 
			// tell the driver the new filter
			if ( ! DeviceIoControl(	SysHandle, REGMON_setfilter,
									&upcaseFilter, sizeof(FILTER), NULL, 
									0, &nb, NULL ) )
			{
				Abort( hDlg, _T("Couldn't access device driver") );
				return TRUE;
			}

			EndDialog( hDlg, TRUE );
			return TRUE;

		} else if( LOWORD( wParam ) == IDCANCEL ) {

			EndDialog( hDlg, TRUE );

		} else if( LOWORD( wParam ) == IDRESET ) {

			// reset filter to default of none
			sprintf( FilterDefinition.processfilter, "*" );
			sprintf( FilterDefinition.processexclude, "" );
			sprintf( FilterDefinition.pathfilter, "*" );
			sprintf( FilterDefinition.excludefilter, "");
			FilterDefinition.logsuccess = TRUE;
			FilterDefinition.logerror = TRUE;
			FilterDefinition.logreads = TRUE;
			FilterDefinition.logwrites = TRUE;
			MaxLines = 0;
 
			// initialize the controls to reflect the current filter
			SetDlgItemText( hDlg, IDC_PROCFILTER, FilterDefinition.processfilter );
			SetDlgItemText( hDlg, IDC_PROCEXCLUDE, FilterDefinition.processexclude );
			SetDlgItemText( hDlg, IDC_PATHFILTER, FilterDefinition.pathfilter );
			SetDlgItemText( hDlg, IDC_EXCLUDEFILTER, FilterDefinition.excludefilter );
			CheckDlgButton( hDlg, IDC_SUCCESS, FilterDefinition.logsuccess );
			CheckDlgButton( hDlg, IDC_ERROR,   FilterDefinition.logerror );
			CheckDlgButton( hDlg, IDC_LOGREADS, FilterDefinition.logreads );
			CheckDlgButton( hDlg, IDC_LOGWRITES,   FilterDefinition.logwrites );
			SetDlgItemText( hDlg, IDC_HISTORY, "0" );
		}
		break;

	case WM_CLOSE:
		EndDialog( hDlg, TRUE );
		return TRUE;
	}
	return FALSE;   
}


/****************************************************************************
*
*	FUNCTION:	About
*
*	PURPOSE:	Processes messages for "About" dialog box
*
****************************************************************************/
BOOL APIENTRY About( HWND hDlg, UINT message, UINT wParam, LONG lParam )
{
	switch ( message )  {
	   case WM_INITDIALOG:
		  return TRUE;

	   case WM_COMMAND:              
		  if ( LOWORD( wParam ) == IDOK )	 {
			  EndDialog( hDlg, TRUE );
			  return TRUE;
		  }
		  break;

	   case WM_CLOSE:
		  EndDialog( hDlg, TRUE );
		  return TRUE;
	}
	return FALSE;   
}


/******************************************************************************
*
*	FUNCTION:	GetDLLVersion
*
*	PURPOSE:	Gets the version number of the specified DLL.
*
******************************************************************************/
HRESULT GetDLLVersion( PCHAR DllName, LPDWORD pdwMajor, LPDWORD pdwMinor)
{
	HINSTANCE			hDll;
	HRESULT				hr = S_OK;
	DLLVERSIONINFO_		dvi;

	*pdwMajor = 0;
	*pdwMinor = 0;

	//Load the DLL.
	hDll = LoadLibrary(DllName);

	if( hDll ) {

	   pDllGetVersionProc = (PVOID)GetProcAddress(hDll, _T("DllGetVersion"));

	   if(pDllGetVersionProc) {
  
		  ZeroMemory(&dvi, sizeof(dvi));
		  dvi.cbSize = sizeof(dvi);

		  hr = (*pDllGetVersionProc)(&dvi);
  
		  if(SUCCEEDED(hr)) {

			 *pdwMajor = dvi.dwMajorVersion;
			 *pdwMinor = dvi.dwMinorVersion;
		  }
 	  } else {

		  // If GetProcAddress failed, the DLL is a version previous to the one 
		  // shipped with IE 3.x.
		  *pdwMajor = 4;
		  *pdwMinor = 0;
      }
   
	  FreeLibrary(hDll);
	  return hr;
	}

	return E_FAIL;
}


/****************************************************************************
*
*    FUNCTION: MainWndProc(HWND, unsigned, WORD, LONG)
*
*    PURPOSE:  Processes messages for the statistics window.
*
****************************************************************************/
LONG APIENTRY MainWndProc( HWND hWnd, UINT message, UINT wParam, LONG lParam) 
{
	DWORD			nb, versionNumber;
	DWORD			length, type, tag, driverStart;
	TCHAR			Path[ MAX_PATH ];
	HKEY			hDriverKey;
	static TCHAR	group[] = "System Bus Extender";
	static TCHAR	driverPath[ MAX_PATH ];
	TCHAR			systemRoot[ MAX_PATH ];
	static TCHAR	logFile[ MAX_PATH ];
	static HWND		hWndToolbar;
	LPTOOLTIPTEXT	lpToolTipText;
	static TCHAR	szBuf[128];
	LPFINDREPLACE	findMessageInfo;
	DWORD			majorver, minorver;
	TCHAR			*File;
	WIN32_FIND_DATA findData;
	HANDLE			findHandle;
	DWORD			startTime;
	POINT			hitPoint;
	RECT			listRect;
	HDC				hDC;
	PAINTSTRUCT		Paint;
	MENUITEMINFO	bootMenuItem;

	switch ( message ) {

		case WM_CREATE:

			// get hourglass icon ready
			hHourGlass = LoadCursor( NULL, IDC_WAIT );

			// post hourglass icon
			SetCapture(hWnd);
			hSaveCursor = SetCursor(hHourGlass);

			// Create the toolbar control - use modern style if available.
			GetDLLVersion( "comctl32.dll", &majorver, &minorver );
			if( majorver > 4 || (majorver == 4 && minorver >= 70) ) {
				hWndToolbar = CreateToolbarEx( 
					hWnd, TOOLBAR_FLAT | WS_CHILD | WS_BORDER | WS_VISIBLE | TBSTYLE_TOOLTIPS,  
					ID_TOOLBAR, 9, hInst, IDB_TOOLBAR, (LPCTBBUTTON)&tbButtons,
					NUMBUTTONS, 16,16,16,15, sizeof(TBBUTTON)); 
			} else {
				hWndToolbar = CreateToolbarEx( 
					hWnd, WS_CHILD | WS_BORDER | WS_VISIBLE | TBSTYLE_TOOLTIPS,  
					ID_TOOLBAR, 9, hInst, IDB_TOOLBAR, (LPCTBBUTTON)&tbButtonsOld,
					NUMBUTTONSOLD, 16,16,16,15, sizeof(TBBUTTON)); 
			}
			if (hWndToolbar == NULL )
				MessageBox (NULL, _T("Toolbar not created!"), NULL, MB_OK );

			// Create the ListBox within the main window
			hWndList = CreateList( hWnd );
			if ( hWndList == NULL )
				MessageBox( NULL, _T("List not created!"), NULL, MB_OK );

		    // open the handle to the device
			if( IsNT ) {

				// Add the log boot menu item
				bootMenuItem.cbSize = sizeof( bootMenuItem );
				bootMenuItem.fMask = MIIM_TYPE;
				bootMenuItem.fType = MFT_SEPARATOR;
				InsertMenuItem( GetSubMenu( GetMenu(hWnd), 1 ), 
								GetMenuItemCount( GetSubMenu( GetMenu(hWnd), 1 )),
								TRUE, &bootMenuItem );
				bootMenuItem.fMask = MIIM_TYPE|MIIM_ID;
				bootMenuItem.fType = MFT_STRING;
				bootMenuItem.wID = IDM_BOOTLOG;
				bootMenuItem.dwTypeData = (PCHAR) "Log &Boot";
				InsertMenuItem( GetSubMenu( GetMenu(hWnd), 1 ), 
								GetMenuItemCount( GetSubMenu( GetMenu(hWnd), 1 )),
								TRUE, &bootMenuItem );

				GetCurrentDirectory( sizeof Path, Path );
				sprintf( Path+lstrlen(Path), _T("\\%s"), SYS_FILE );

				findHandle = FindFirstFile( Path, &findData );
				if( findHandle == INVALID_HANDLE_VALUE ) {

					if( !SearchPath( NULL, SYS_FILE, NULL, sizeof(Path), Path, &File ) ) {

						sprintf( msgbuf, _T("%s was not found."), SYS_FILE );
						return Abort( hWnd, msgbuf );
					}

				} else FindClose( findHandle );

				// read driver start type to see if boot-logging is enabled
				driverStart = SERVICE_DEMAND_START;
				if( RegOpenKey( HKEY_LOCAL_MACHINE, DriverRegistryKey, &hDriverKey ) == 
					ERROR_SUCCESS ) {

					length = sizeof( driverStart );
					RegQueryValueEx( hDriverKey, "Start", NULL, &type,
						(PBYTE) &driverStart, &length);
					RegCloseKey( hDriverKey );
				} 
				BootLog = (driverStart != SERVICE_DEMAND_START);

				// check boot logging menu item if boot start
				CheckMenuItem( GetMenu(hWnd), IDM_BOOTLOG,
						MF_BYCOMMAND|(BootLog?MF_CHECKED:MF_UNCHECKED) ); 

				// copy the driver to <winnt>\system32\drivers so that we can do
				// boot-time monitoring with the flip of a bit
				// get the system root
				if( !GetEnvironmentVariable( "SYSTEMROOT", systemRoot, sizeof(systemRoot))) {

					strcpy( msgbuf, _T("Could not resolve SYSTEMROOT environment variable") );
					return Abort( hWnd, msgbuf );
				}
				sprintf( logFile, _T("%s\\REGMON.LOG"), systemRoot );
				sprintf( driverPath, _T("%s\\system32\\drivers\\%s"), 
								systemRoot, SYS_FILE );
				if( !CopyFile( Path, driverPath, FALSE )) {

					sprintf( msgbuf, _T("Unable to copy %s to %s\n\n")
						_T("Make sure that regsys.sys is in the current directory."), 
						SYS_NAME, driverPath );
					return Abort( hWnd, msgbuf );
				}

				if ( ! LoadDeviceDriver( SYS_NAME, driverPath, &SysHandle ) )  {

					sprintf( msgbuf, _T("Opening %s (%s): error %d"), SYS_NAME, Path,
									GetLastError( ) );
					return Abort( hWnd, msgbuf );
				}

				// Correct driver version?
				if ( ! DeviceIoControl(	SysHandle, REGMON_version,
										NULL, 0, &versionNumber, sizeof(DWORD), &nb, NULL ) ||
						versionNumber != REGMONVERSION )
				{
					MessageBox( hWnd, _T("Regmon located a driver with the wrong version.\n")
						_T("\nIf you just installed a new version you must reboot before you are")
						_T("able to use it."), _T("Regmon"), MB_ICONERROR);
					return -1;
				}

			} else {

				// Win9x
				SysHandle = CreateFile( VXD_FILE, 0, 0, NULL,
								0, FILE_FLAG_OVERLAPPED|
								FILE_FLAG_DELETE_ON_CLOSE,
								NULL );
				if ( SysHandle == INVALID_HANDLE_VALUE )  {
					wsprintf( msgbuf, "%s is not loaded properly.", VXD_NAME );
					Abort( hWnd, msgbuf );
					return FALSE;
				}
			}

			// Have driver zero information
			if ( ! DeviceIoControl(	SysHandle, REGMON_zerostats,
									NULL, 0, NULL, 0, &nb, NULL ) )
			{
				return Abort( hWnd, _T("Couldn't access device driver") );
			}

			// Give the user to change initial filter
			if( strcmp(FilterDefinition.processfilter, "*") ||
				strcmp(FilterDefinition.processexclude, "") ||
				strcmp(FilterDefinition.pathfilter, "*")    ||
				strcmp(FilterDefinition.excludefilter, "")  ||
				!FilterDefinition.logsuccess ||
				!FilterDefinition.logerror   ||
				!FilterDefinition.logreads   ||
				!FilterDefinition.logwrites ) {

				DialogBox( hInst, _T("InitFilter"), hWnd, (DLGPROC) FilterProc );
			
			} else {

				// tell the driver the initial filter
				if ( ! DeviceIoControl(	SysHandle, REGMON_setfilter,
										&FilterDefinition, sizeof(FILTER), NULL, 
										0, &nb, NULL ) )
				{
					return Abort( hWnd, _T("Couldn't access device driver") );
				}
			}

			// Start up timer to periodically update screen
			SetTimer( hWnd,	1, 500/*ms*/, NULL );

			// Have driver turn on hooks
			if ( ! DeviceIoControl(	SysHandle, REGMON_hook,
									NULL, 0, NULL, 0, &nb, NULL ) )
			{
				return Abort( hWnd, _T("Couldn't access device driver") );
			}
			
			// Initialization done
			SetCursor( hSaveCursor );
			ReleaseCapture();
			return FALSE;

		case WM_NOTIFY:
			// Make sure its intended for us
			if ( wParam == ID_LIST )  {
				NM_LISTVIEW	* pNm = (NM_LISTVIEW *)lParam;
				switch ( pNm->hdr.code )  {

			        case LVN_BEGINLABELEDIT:
						// Don't allow editing of information
						return TRUE;

					case NM_DBLCLK:
					case NM_RETURN:

						// open the specified key in Regedit, if we can
						RegeditJump( hWnd );
						return TRUE;
				}
			} else {

				switch (((LPNMHDR) lParam)->code) 
				{
					case TTN_NEEDTEXT:    
						// Display the ToolTip text.
						lpToolTipText = (LPTOOLTIPTEXT)lParam;
    					LoadString (hInst, lpToolTipText->hdr.idFrom, szBuf, sizeof(szBuf));
				    	lpToolTipText->lpszText = szBuf;
						break;

					default:
						return FALSE;
				}
			}
			return FALSE;

		case WM_COMMAND:

			switch ( LOWORD( wParam ) )	 {

				// stats related commands to send to driver
				case IDM_CLEAR:
					// Have driver zero information
					if ( ! DeviceIoControl(	SysHandle, REGMON_zerostats,
											NULL, 0, NULL, 0, &nb, NULL ) )
					{
						Abort( hWnd, _T("Couldn't access device driver") );
						return TRUE;
					}
					// Update statistics windows
					UpdateStatistics( hWnd, hWndList, TRUE );
					return FALSE;

				case IDM_HELP:
					WinHelp(hWnd, _T("regmon.hlp"), HELP_CONTENTS, 0L);
					return 0;

				case IDM_FIND:
					// search the listview
					if( !hWndFind ) {
						PrevMatch = FALSE;
						PopFindDialog( hWnd );
					} else if( PrevMatch ) {

						// treat this like a find-next
						SetCapture(hWndFind);
						hSaveCursor = SetCursor(hHourGlass);
						EnableWindow( hWndFind, FALSE );
						if (FindInListview( hWnd, &FindTextInfo ) ) {
							Autoscroll = FALSE;
							CheckMenuItem( GetMenu(hWnd), IDM_AUTOSCROLL,
											MF_BYCOMMAND|MF_UNCHECKED ); 
							SendMessage( hWndToolbar, TB_CHANGEBITMAP, IDM_AUTOSCROLL, 3 );
						}
						EnableWindow( hWndFind, TRUE );
						SetCursor( hSaveCursor );
						ReleaseCapture(); 
					}
					return 0;

				case IDM_CAPTURE:
					// Read statistics from driver
					Capture = !Capture;
					CheckMenuItem( GetMenu(hWnd), IDM_CAPTURE,
									MF_BYCOMMAND|(Capture?MF_CHECKED:MF_UNCHECKED) );

					// Have driver turn on hooks
					if ( ! DeviceIoControl(	SysHandle, Capture ? REGMON_hook : 
											REGMON_unhook,
											NULL, 0, NULL, 0, &nb, NULL ) )
					{
						Abort( hWnd, _T("Couldn't access device driver") );
						return TRUE;
					}
					SendMessage( hWndToolbar, TB_CHANGEBITMAP, IDM_CAPTURE, (Capture?2:1) );
					InvalidateRect( hWndToolbar, NULL, TRUE );
					return FALSE;

				case IDM_AUTOSCROLL:
					Autoscroll = !Autoscroll;
					CheckMenuItem( GetMenu(hWnd), IDM_AUTOSCROLL,
									MF_BYCOMMAND|(Autoscroll?MF_CHECKED:MF_UNCHECKED) ); 
					SendMessage( hWndToolbar, TB_CHANGEBITMAP, IDM_AUTOSCROLL, (Autoscroll?4:3) );
					InvalidateRect( hWndToolbar, NULL, TRUE );					
					return FALSE;

				case IDM_BOOTLOG:
					BootLog = !BootLog;
					CheckMenuItem( GetMenu(hWnd), IDM_BOOTLOG,
									MF_BYCOMMAND|(BootLog?MF_CHECKED:MF_UNCHECKED) ); 
					if( BootLog ) {

						sprintf( msgbuf, 
							_T("Regmon has been configured to log Registry activity to %s during the next boot"),
							logFile );
						MessageBox( hWnd, msgbuf, _T("Regmon"), MB_OK|MB_ICONINFORMATION);
					}
					BootLogMenuUsed = TRUE;
					return FALSE;

				case IDM_EXIT:
					// Close ourself
					SendMessage( hWnd, WM_CLOSE, 0, 0 );
					return FALSE;

				case IDM_FILTER:
					DialogBox( hInst, _T("Filter"), hWnd, (DLGPROC) FilterProc );
					return FALSE;

				case IDM_ONTOP:
					OnTop = !OnTop;
					if( OnTop ) SetWindowPos( hWnd, HWND_TOPMOST, 0, 0, 0, 0, 
									SWP_NOMOVE|SWP_NOSIZE );
					else  SetWindowPos( hWnd, HWND_NOTOPMOST, 0, 0, 0, 0, 
									SWP_NOMOVE|SWP_NOSIZE );
					CheckMenuItem( GetMenu(hWnd), IDM_ONTOP,
							MF_BYCOMMAND|(OnTop?MF_CHECKED:MF_UNCHECKED) );
					return 0;

				case IDM_JUMP:

					// open the specified key in Regedit, if we can
					RegeditJump( hWnd );
					return FALSE;

				case IDM_ABOUT:
					// Show the names of the authors
					DialogBox( hInst, _T("AboutBox"), hWnd, (DLGPROC)About );
					return FALSE;

				case IDM_SAVE:
					SaveFile( hWnd, hWndList, FALSE );
					return FALSE;

				case IDM_SAVEAS:
					SaveFile( hWnd, hWndList, TRUE );
					return FALSE;

				default:
					// Default behavior
					return DefWindowProc( hWnd, message, wParam, lParam );
			}
			break;

		case WM_TIMER:
			// Time to query the device driver for more data
			if ( Capture )  {

				// don't process for more than a second without pausing
				startTime = GetTickCount();
				for (;;)  {

					// Have driver fill Stats buffer with information
					if ( ! DeviceIoControl(	SysHandle, REGMON_getstats,
											NULL, 0, &Stats, sizeof Stats,
											&StatsLen, NULL ) )
					{
						Abort( hWnd, _T("Couldn't access device driver") );
						return TRUE;
					}
					if ( StatsLen == 0 )
						break;

					// Update statistics windows
					UpdateStatistics( hWnd, hWndList, FALSE );

					if( GetTickCount() - startTime > 1000 ) break;
				}
			}

			// delete balloon if necessary
			if( hBalloon ) {
				GetCursorPos( &hitPoint );
				GetWindowRect( hWndList, &listRect );
				if( hitPoint.x < listRect.left ||
					hitPoint.x > listRect.right ||
					hitPoint.y < listRect.top ||
					hitPoint.y > listRect.bottom ) {
	
					DestroyWindow( hBalloon );
				}
			}
			return FALSE;

		case WM_SIZE:
			// Move or resize the List
			MoveWindow( hWndToolbar, 0, 0, LOWORD(lParam), HIWORD(lParam), TRUE );
            MoveWindow( hWndList, 0, TOOLBARHEIGHT, LOWORD(lParam), HIWORD(lParam)-TOOLBARHEIGHT, TRUE );
			if( hBalloon ) DestroyWindow( hBalloon );
			return FALSE;

		case WM_MOVE:
		case WM_MOUSEMOVE:
			if( hBalloon ) DestroyWindow( hBalloon );
			return FALSE;

		case WM_CLOSE:

			// Have driver unhook if necessary
			if( Capture ) {
				if ( ! DeviceIoControl(	SysHandle, REGMON_unhook,
									NULL, 0, NULL, 0, &nb, NULL ) )
				{
					Abort( hWnd, _T("Couldn't access device driver") );
					return TRUE;
				}
			}

			KillTimer( hWnd, 1 );
			CloseHandle( SysHandle );	
#if _DEBUG
			if ( IsNT &&  !UnloadDeviceDriver( SYS_NAME ) )  {
				wsprintf( msgbuf, _T("Error unloading \"%s\""), SYS_NAME );
				MessageBox( hWnd, msgbuf, _T("Regmon"), MB_OK );
			}
#endif
			// Make sure the user knows boot logging will take place
			if( IsNT ) {

				if( !BootLogMenuUsed && BootLog ) {

					sprintf( msgbuf, 
						_T("Regmon is configured to log Registry activity to %s during the next boot"),
						logFile );

					MessageBox( hWnd, msgbuf, _T("Regmon"), MB_ICONINFORMATION);
				}

				// if boot logging isn't enabled, delete the driver from 
				// the drivers directory
				if( !BootLog ) {

					if( RegCreateKey( HKEY_LOCAL_MACHINE, DriverRegistryKey, &hDriverKey ) == 
						ERROR_SUCCESS ) {

						driverStart = SERVICE_DEMAND_START;
						RegSetValueEx( hDriverKey, _T("Start"), 0, REG_DWORD, 
							(PBYTE) &driverStart, sizeof(driverStart));
						RegDeleteValue( hDriverKey, _T("Group"));
						RegDeleteValue( hDriverKey, _T("Tag"));
						DeleteFile( driverPath );
					}
					
				} else {

					// boot logging on - configure the regmon service key.
					if( RegCreateKey( HKEY_LOCAL_MACHINE, DriverRegistryKey, &hDriverKey ) == 
						ERROR_SUCCESS ) {

						// the driver is already in the winnt\system32\drivers directory
						driverStart = SERVICE_BOOT_START;
						RegDeleteValue( hDriverKey, _T("DeleteFlag" ));
						RegSetValueEx( hDriverKey, _T("Start"), 0, REG_DWORD, 
							(PBYTE) &driverStart, sizeof(driverStart));
						RegSetValueEx( hDriverKey, "Group", 0, REG_SZ, group, sizeof( group ));
						tag = 1;
						RegSetValueEx( hDriverKey, "Tag", 0, REG_DWORD, 
							(PBYTE) &tag, sizeof(tag));
						RegSetValueEx( hDriverKey, "Type", 0, REG_DWORD,
							(PBYTE) &tag, sizeof(tag));
						sprintf( Path, _T("System32\\Drivers\\%s"),
							SYS_FILE );	
						RegSetValueEx( hDriverKey, _T("ImagePath"), 0, REG_EXPAND_SZ,
							Path, strlen(Path));
						RegCloseKey( hDriverKey );

					} else {

						Abort( hWnd, _T("Regmon could not configure boot logging"));
					}
				}
				if( hDriverKey != INVALID_HANDLE_VALUE ) RegCloseKey( hDriverKey );		
			}

			Save_Position_Settings( hWnd );
			return DefWindowProc( hWnd, message, wParam, lParam );

		case WM_SETFOCUS:
			SetFocus( hWndList );
			break;

		case WM_DESTROY:
			PostQuitMessage(0);
			return FALSE;

		case WM_PAINT:
			if( !IsNT && Deleting ) {
				hDC = BeginPaint( hWnd, &Paint );
				EndPaint( hWnd, &Paint );
				return TRUE;
			}
			return DefWindowProc( hWnd, message, wParam, lParam );

		default:
			// is it a find-string message?
			if (message == findMessageID ){ 

				// get a pointer to the find structure
				findMessageInfo = (LPFINDREPLACE)lParam;

				// If the FR_DIALOGTERM flag is set, invalidate the find window handle
				if( findMessageInfo->Flags & FR_DIALOGTERM) {
					hWndFind = NULL;
					PrevMatch = FALSE;
				    FindFlags = FindTextInfo.Flags & (FR_DOWN|FR_MATCHCASE|FR_WHOLEWORD);
					return 0;
				}

				// if the FR_FINDNEXT flag is set, go do the search
				if( findMessageInfo->Flags & FR_FINDNEXT ) {
					SetCapture(hWndFind);
					hSaveCursor = SetCursor(hHourGlass);
					EnableWindow( hWndFind, FALSE );
					if( FindInListview( hWnd, findMessageInfo ) ) {
						Autoscroll = FALSE;
						CheckMenuItem( GetMenu(hWnd), IDM_AUTOSCROLL,
										MF_BYCOMMAND|MF_UNCHECKED ); 
						SendMessage( hWndToolbar, TB_CHANGEBITMAP, IDM_AUTOSCROLL, 3 );
					}
					EnableWindow( hWndFind, TRUE );
					ReleaseCapture(); 
					return 0;
				}
				return 0;
			}

			// Default behavior
			return DefWindowProc( hWnd, message, wParam, lParam );
	}
	return FALSE;
}



/****************************************************************************
*
*    FUNCTION: InitApplication(HANDLE)
*
*    PURPOSE: Initializes window data and registers window class
*
****************************************************************************/
BOOL InitApplication( HANDLE hInstance )
{
	WNDCLASS  wc;
	
	// Fill in window class structure with parameters that describe the
	// main (statistics) window. 
	wc.style			= 0;                     
	wc.lpfnWndProc		= (WNDPROC)MainWndProc; 
	wc.cbClsExtra		= 0;              
	wc.cbWndExtra		= 0;              
	wc.hInstance		= hInstance;       
	wc.hIcon			= LoadIcon( hInstance, _T("ICON") );
	wc.hCursor			= LoadCursor( NULL, IDC_ARROW );
	wc.hbrBackground	= (HBRUSH)(COLOR_INACTIVEBORDER + 1); // Default color
	wc.lpszMenuName		= _T("LISTMENU");  
	wc.lpszClassName	= _T("RegmonClass");
	if ( ! RegisterClass( &wc ) )
		return FALSE;

	wc.lpszMenuName	  = NULL;
 	wc.lpfnWndProc    = (WNDPROC) BalloonDialog;
	wc.hbrBackground  = CreateSolidBrush( 0x00E0FFFF );
	wc.lpszClassName  = "BALLOON";
	RegisterClass( &wc );
	
	return TRUE;
}


/****************************************************************************
*
*    FUNCTION:  InitInstance(HANDLE, int)
*
*    PURPOSE:  Saves instance handle and creates main window
*
****************************************************************************/
HWND InitInstance( HANDLE hInstance, int nCmdShow )
{
	// get the window position settings from the registry
	Get_Position_Settings();

	hInst = hInstance;
	hWndMain = CreateWindow( _T("RegmonClass"), 
							_T("Registry Monitor - Systems Internals: http://www.sysinternals.com"), 
							WS_OVERLAPPEDWINDOW,
							PositionInfo.left, PositionInfo.top, 
							PositionInfo.width, PositionInfo.height,
							NULL, NULL, hInstance, NULL );

	// if window could not be created, return "failure" 
	if ( ! hWndMain )
		return NULL;
	
	// make the window visible; update its client area; and return "success"
	ShowWindow( hWndMain, nCmdShow );
	UpdateWindow( hWndMain ); 

	// maximize it if necessary
	if( PositionInfo.maximized ) {

		ShowWindow( hWndMain, SW_SHOWMAXIMIZED );
	}
	if( OnTop ) {
		
		SetWindowPos( hWndMain, HWND_TOPMOST, 0,0,0,0, SWP_NOMOVE|SWP_NOSIZE );
		CheckMenuItem( GetMenu(hWndMain), IDM_ONTOP,
						MF_BYCOMMAND|(OnTop?MF_CHECKED:MF_UNCHECKED) );
	}
	return hWndMain;      
}


/****************************************************************************
*
*	FUNCTION: WinMain(HANDLE, HANDLE, LPSTR, int)
*
*	PURPOSE:	calls initialization function, processes message loop
*
****************************************************************************/
int APIENTRY WinMain( HINSTANCE hInstance, HINSTANCE hPrevInstance,
						LPSTR lpCmdLine, int nCmdShow )
{
	MSG 	msg;      
	HWND	hWnd;
	HACCEL	hAccel;
 	DWORD	NTVersion;
        
	if ( ! InitApplication( hInstance ) )
		return FALSE;   
	
	// get NT version
	NTVersion = GetVersion();
	if( NTVersion >= 0x80000000 ) {

		IsNT = FALSE;

	} else {

		IsNT = TRUE;
	}

	// initializations that apply to a specific instance 
	if ( (hWnd = InitInstance( hInstance, nCmdShow )) == NULL )
		return FALSE;

	// load accelerators
	hAccel = LoadAccelerators( hInstance, _T("ACCELERATORS"));

	// register for the find window message
    findMessageID = RegisterWindowMessage( FINDMSGSTRING );

	// acquire and dispatch messages until a WM_QUIT message is received.
	while ( GetMessage( &msg, NULL, 0, 0 ) )  {
		if( !TranslateAccelerator( hWnd, hAccel, &msg ) &&
			(!hWndFind || !IsWindow(hWndFind) || !IsDialogMessage( hWndFind, &msg ))) {
			TranslateMessage( &msg );
			DispatchMessage( &msg ); 
		}
	}
	return msg.wParam;										 
}
