### MacOS 下编译成 libwasmer.dylib 库

```sh
$ make build-capi-cranelift
$ cp target/release/libwasmer.dylib vm-wasmer的目录/wasmer-go/packaged/对应架构/libwasmer.dylib
```

### Linux 下编译成 libwasmer.so 库

```sh
$ make build-capi-cranelift
$ cp target/release/libwasmer.so vm-wasmer的目录/wasmer-go/packaged/对应架构/libwasmer.so
```
