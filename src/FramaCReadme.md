
```
reset; frama-c -kernel-h | less

reset; frama-c -cpp-extra-args="-Iinclude" -kernel-msg-key pp -rte -wp src/*.c

reset; frama-c -kernel-msg-key pp -rte -eva *.c

reset; frama-c-gui -eva-precision 3 -eva *.c
```