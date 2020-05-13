A "binary bomb" is a Linux executable C program that consists of six
"phases." Each phase expects the user to enter a particular string
on stdin.  If the user enters the expected string, then that phase
is "defused."  Otherwise the bomb "explodes" by printing "BOOM!!!".
The goal is to defuse as many phases as possible.
