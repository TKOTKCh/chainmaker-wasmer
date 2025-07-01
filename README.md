### MacOS 下编译成 libwasmer.dylib 库

```sh
$ make build-capi-cranelift
$ cp target/release/libwasmer.dylib {用户自定义目录}/libwasmer.dylib
$ cd {用户自定义目录}
$ install_name_tool -id "@rpath/libwasmer.dylib" ./libwasmer.dylib
```

### Linux 下编译成 libwasmer.so 库

```sh
$ make build-capi-cranelift
$ cp target/release/libwasmer.so {用户自定义目录}/libwasmer.so
```
