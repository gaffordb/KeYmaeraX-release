#!/bin/sh
java -Xss20M -jar keymaerax-4.2b2.jar -mathkernel /Applications/Mathematica.app/Contents/MacOS/MathKernel -jlink /Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64 -prove CheatSheet.kyx -tactic CheatSheetScriptTactic.scala -out CheatSheet.kyx.proof