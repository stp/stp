#!/bin/bash
# You can use this script to symbolically link the requested libraries.  
# You can then compile STP using:
#   make STATIC=true
# if you want to use the SMT-LIB parser
ln -s `g++ -print-file-name=libstdc++.a`
ln -s `g++ -print-file-name=libc.a`
