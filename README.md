# Project Description
GPM/CLR is an implementation of the historical Gardens-Point Modula-2 compiler for the .NET runtime.  It provides an example of how a non-typesafe, unmanaged data compiler may be implemented on the CLR.


# Features
Modula-2 is a Pascal-family language invented by Niklaus Wirth at ETH, Zurich.  It is a statically typed language which uses _modules_ as it organizational paradigm.  It was one of the first languages to use the separation of definition and implementation parts to provide for type-safe separate compilation.  This particular feature was incorporated essentially unchanged into language Ada.  Despite its strong typing, the language necessarily generates executables that are not verifiable.  The language is comparable with ANSI C in that respect.

Modula-2 was standardized by the ISO, but the standard was handicapped by an opaque formal definition, and an IO library that many considered to be eccentric.  Nevertheless the language was influential on other language designs, and was widely used as a first programming language, particularly in Europe.

Gardens Point Modula-2 was a widely available implementation of the Modula-2 language from about 1986 to 1996.  It was available on about eleven different platforms, including most of the major workstation architectures.  All of these versions used an identical compiler front-end which produced a stack-based intermediate form.  The intermediate code generated by the front-end was parameterized at runtime by a configuration file with target details.  Separate back-ends for each machine architecture generated object code from the intermediate form.

GPM/CLR is an exercise in adding a different emitter to the standard front-end, emitting CIL assembly language for the CLR.  The exercise has two purposes: first, it is a demonstration of how the CLR may be used to implement languages that are unsafe and which use unmanaged data; second, it provides a path for executing legacy applications that are written in Modula-2.

## Limitations
The compiler has only been tested on the Intel/Windows platform.  It very well might work on other platforms ... or maybe not.

Not all of the features of Modula-2 have been implemented.  For example coroutine support, a feature of the language, has not been implemented.  It is _possible_ to fudge this by messing with the threading system but is, well, messy!

Not all of the libraries normally supplied with GPM are in this distribution.  For example, almost none of the ISO IO libraries are available because of the absence of C# versions of two low-level libraries.  Also the pipe-handling libraries are unimplemented in this release. 