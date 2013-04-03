copy %BASEDIR%\lib\%CPU%\free\regsys.sys .
copy %BASEDIR%\lib\%CPU%\free\regsys.sys ..\gui\.
copy %BASEDIR%\lib\%CPU%\free\regsys.sys ..\gui\release\.
copy %BASEDIR%\lib\%CPU%\free\regsys.sys ..\gui\debug\.
rmdir /s /q obj
del *.log


