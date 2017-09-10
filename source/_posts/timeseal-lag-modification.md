---
title: Online chess clock exploit
date: 2014-06-10
tags: ["timeseal", "chess", "Reverse Engineering"]
subtitle: Modify client side lag calculation for infinite time
---

The following exploit works for any online chess server that use timeseal. This bug has been reported to all major chess sites and is known since many years. As for example this hack is not possible on lichess.[^1] However there might still be a server out there that is using timeseal. Please contact the Administrator and ask him for a fix.

> Timeseal is a program that has been developed to improve chess on internet.  Netlag often causes players to lose valuable seconds or even minutes on their chess clocks.  Transmission time is counted against you, unless the chess server can tell exactly when information is transmitted.  The timeseal program acts as a relay station and keeps track of transmission times.  What timeseal does is record your thinking time, so that transmission time is not counted against you.  Timeseal will not prevent netlag but it makes the games fairer when lag occurs. [^2]

![](https://i.imgur.com/M2oOKFx.png)

Timeseal calculates the lag as a difference between two timestamps. Modifying the lag value can be done by adding an random offset to the timestamp calculation. The code can be hex edited (hardcoded) into the timeseal binary.

```asm
00401421   E8 CA0D0000      CALL timeseal.004021F0
00401426   25 FF030000      AND EAX,3FF
0040142B   05 01010000      ADD EAX,101
00401430   8B15 E0A14000    MOV EDX,DWORD PTR DS:[40A1E0]
00401436   03D0             ADD EDX,EAX
00401438   8915 E0A14000    MOV DWORD PTR DS:[40A1E0],EDX
0040143E   8BC2             MOV EAX,EDX
```

The address for the random hook is `timeseal.004021F0 := rand()` while `AND EAX, 3FF` is the asm modulo function `rand()%1024` + fixed offset hex 101. The modification offers the following unfair advantages:

* Impossible to loose on time
* Always move faster than your opponent
* Seems legit, opponents may think that you are simply lagging, cause of random offset

Full fledged example that hooks into the `ADVAPI32.dll` with a small window for different lag settings.

```c++
#include "stdafx.h"
#pragma comment(lib, "detours.lib")

#undef UNICODE
#include <cstdio>
#include <windows.h>
#include <detours.h>
#include <process.h>
#include <iostream>
#include <string>

using std::cin;
using std::cout;
#pragma pack(1)

int Time = 0;
int offset = 480;
int randmod = 1;

#define MYMENU_EXIT         (WM_APP + 101)
#define MYMENU_MESSAGEBOX   (WM_APP + 102)

HINSTANCE  inj_hModule;
HWND       prnt_hWnd;

LRESULT CALLBACK DLLWindowProc (HWND, UINT, WPARAM, LPARAM);

BOOL RegisterDLLWindowClass(wchar_t szClassName[]) {
    WNDCLASSEX wc;
    wc.hInstance =  inj_hModule;
    wc.lpszClassName = (LPCWSTR)L"InjectedDLLWindowClass";
    wc.lpszClassName = (LPCWSTR)szClassName;
    wc.lpfnWndProc = DLLWindowProc;
    wc.style = CS_DBLCLKS;
    wc.cbSize = sizeof (WNDCLASSEX);
    wc.hIcon = LoadIcon (NULL, IDI_APPLICATION);
    wc.hIconSm = LoadIcon (NULL, IDI_APPLICATION);
    wc.hCursor = LoadCursor (NULL, IDC_ARROW);
    wc.lpszMenuName = NULL;
    wc.cbClsExtra = 0;
    wc.cbWndExtra = 0;
    wc.hbrBackground = (HBRUSH) COLOR_BACKGROUND;
    if (!RegisterClassEx (&wc)) return 0;
}

#define ONE_PLUS_ZERO 600
#define ZERO_PLUS_ONE 601
#define MINIMUM 602
#define BIGTIME 603
#define TIMELOOSE 604

HMENU CreateDLLWindowMenu() {
    HMENU hMenu;
    hMenu = CreateMenu();
    HMENU hMenuPopup;
    if(hMenu==NULL) return FALSE;
    hMenuPopup = CreatePopupMenu();
    AppendMenu (hMenuPopup, MF_STRING, MYMENU_EXIT, TEXT("Exit"));
    AppendMenu (hMenu, MF_POPUP, (UINT_PTR) hMenuPopup, TEXT("Exit"));
    hMenuPopup = CreatePopupMenu();
    AppendMenu (hMenuPopup, MF_STRING, ONE_PLUS_ZERO, TEXT("Preset '1 0'"));
    AppendMenu (hMenuPopup, MF_STRING, ZERO_PLUS_ONE, TEXT("Preset '0 1'"));
    AppendMenu (hMenuPopup, MF_STRING, MINIMUM, TEXT("MINIMUM"));
    AppendMenu (hMenuPopup, MF_STRING, BIGTIME, TEXT("BIGTIME"));
    AppendMenu (hMenuPopup, MF_STRING, TIMELOOSE, TEXT("TIMELOOSE"));
    AppendMenu (hMenu, MF_POPUP, (UINT_PTR) hMenuPopup, TEXT("TimeSeal"));
    return hMenu;
}

DWORD WINAPI ThreadProc( LPVOID lpParam ) {
    MSG messages;
    wchar_t *pString = reinterpret_cast<wchar_t * > (lpParam);
    HMENU hMenu = CreateDLLWindowMenu();
    RegisterDLLWindowClass(L"InjectedDLLWindowClass");
    prnt_hWnd = FindWindow(L"Window Injected Into ClassName", L"Window Injected Into Caption");
    HWND hwnd = CreateWindowEx (0, L"InjectedDLLWindowClass", pString, WS_EX_PALETTEWINDOW, CW_USEDEFAULT, CW_USEDEFAULT, 400, 300, prnt_hWnd, hMenu,inj_hModule, NULL );
    ShowWindow (hwnd, SW_SHOWNORMAL);
    while (GetMessage (&messages, NULL, 0, 0)) {
        TranslateMessage(&messages);
        DispatchMessage(&messages);
    }
    return 1;
}

LRESULT CALLBACK DLLWindowProc (HWND hwnd, UINT message, WPARAM wParam, LPARAM lParam) {
    switch (message) {
    case WM_COMMAND:
        switch(wParam) {
        case MYMENU_EXIT:
            SendMessage(hwnd, WM_CLOSE, 0, 0);
            break;
        case ONE_PLUS_ZERO:
            offset = 502;
            randmod = 1320;
            break;
        case ZERO_PLUS_ONE:
            offset = 502;
            randmod = 1320;
            break;
        case MINIMUM:
            offset = 102;
            randmod = 200;
            break;
        case BIGTIME:
            offset = 2000;
            randmod = 3000;
            break;
        case TIMELOOSE:
            offset = 100000;
            randmod = 30000;
            break;
        }
        break;
    case WM_DESTROY:
        PostQuitMessage (0);
        break;
    default:
        return DefWindowProc (hwnd, message, wParam, lParam);
    }
    return 0;
}

void startup() {
    CreateThread(0, NULL, ThreadProc, (LPVOID)L"", NULL, NULL);
    __asm mov eax, 0x00401400
    __asm call eax
    __asm mov Time, eax
}

int __cdecl Hooked_GetTimeForLag() {
    int random = 0;
    __asm mov eax, 0x004021F0
    __asm call eax
    __asm mov random, eax
    Time = Time + (random%randmod);
    Time = Time + offset;
    return Time;
}

HMODULE libraryHandle;
_declspec(dllexport) BOOL WINAPI GetUserNameA(LPSTR input, LPDWORD buffer) {
    typedef BOOL (WINAPI* CFunction) (LPSTR input, LPDWORD buffer);
    CFunction getUserName = (CFunction)GetProcAddress(libraryHandle, "GetUserNameA");
    return getUserName(input, buffer);
}

BOOL WINAPI DllMain(HMODULE module,DWORD action,LPVOID reserved) {
    libraryHandle = LoadLibraryA("ADVAPI32.dll");
    switch(action) {
    case DLL_PROCESS_ATTACH: {
            DetourTransactionBegin();
            DetourUpdateThread(GetCurrentThread());
            startup();
            DetourAttach(&(PVOID&)GetTimeForLag, Hooked_GetTimeForLag);
            DetourTransactionCommit();
            break;
        }
        break;
    case DLL_THREAD_ATTACH:
        break;
    }
    return true;
}
```

## References
[^1]: [Lichess](https://lichess.org/qa/602/is-the-timeseal-exploit-on-other-chess-servers-a-concern-on-lichess)
[^2]: [Free Internet Chess Server](http://www.freechess.org/Help/HelpFiles/timeseal.html)
