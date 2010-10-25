REM
REM make all these C# support libraries
REM
csc /t:library /debug /unsafe /out:M2ClrRts.dll M2RTS.cs m2iop.cs InOut.cs RealMath.cs StdError.cs TextInOut.cs HugeInOut.cs

move M2ClrRts.dll ..\M2ClrBin
move M2ClrRts.pdb ..\M2ClrBin
