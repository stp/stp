; RUN: %solver %s
;
; A script with no command at all, only comments, is a script: SMT-LIB's
; <script> is <command>*. It was a syntax error, "unexpected end of file".
