
```
reset; frama-c -kernel-h | less

reset; frama-c -cpp-extra-args="-Iinclude" -kernel-msg-key pp -rte -wp src/*.c
```