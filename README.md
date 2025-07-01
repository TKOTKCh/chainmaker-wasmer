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

### 支持 ChainMaker 版本说明
wasmer-vm v2.3.1 版本编译的 libwasmer 库用于 ChainMaker 2.3.1 之后的版本。
wasmer-vm v2.2.0 版本编译的 libwasmer 库用于 ChainMaker 2.2.0 ~ 2.3.0 之前的所有版本。
wasmer-vm v2.1.0 版本编译的 libwasmer 库用于 ChainMaker 2.1.x 之前的所有版本。