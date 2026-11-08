# New Nanomite Obfuscation Pass
Built for LLVM 19.1 - Windows x64 <br> <br>

So with nanomites, they are a rather unknown thing as they aren't in any major commercial obfuscators besides Theia, and they were in some old packer back in the early 2000s. <br>
Nanomites tend to be exception based control flow, you force a fault, catch the exception, split the decryption between fault RIP address, Preloading registers at site, and a preset array, so there are 3 forms of truth to traverse the original value.
Then most people just use them to break blocks. <br>
Nanomites are incredibly effective against inexperienced reverse engineers that heavily rely on tooling. As you need to resolve them before you can IR lift, or use an AI MCP. <br>
As they aren't too common they put up a very good fight against the new gen slop reversers you tend to find these days. <br> <br>

We implement 2 new flavours of nanomites that have never been used publicly.
* CFG(control flow guard)
* Instrument Callback (syscall catching)

This gives us a total of 3 dispatch/ handling methods
* Exception
* CFG
* Instrument Callback

This means unlike other obfuscators, you have 3 systems your attacker has to defeat, they can't simply follow the exception handler. <br>
Any AI that is trained before this date will not understand the other methods as they simply aren't publicly documented prior to this. So thats another nice thing, there are a few more ways to do nanomites too if you get creative With windows.<br>


## The Methodology

### Exception Nanomites

Very basic, Places an exception handler at start up. Fires either an invalid instruction, or an access violation to invoke it.<br> 
It will then emit a fake stub at the original site to disturb control flow for anyone unaware of the nanomites firing. <br>
When the exception handler catches the exception, it decrypts the site and jumps out past the dummy stub and into the real code. <br>

<img width="289" height="179" alt="image" src="https://github.com/user-attachments/assets/6cef36c2-10db-4707-b55a-66afb27ec022" />


### Instrument Callback Nanomites

We install an instrument callback. This allows us to get a message whenever any syscall has fired from the kernel from our application, the syscall doesn't have to be valid either. <br>
So we install an invalid syscall at the site, let it fire, catch it in our exception callback, decrypt the target, then jump to the real target. <br>
Polluting the site so that it looks like it jumps to a different block in the function instead.<br>

<img width="443" height="224" alt="image" src="https://github.com/user-attachments/assets/40396cc9-8929-4072-8fbd-ab7a92c16fd4" />
<br>
<img width="379" height="260" alt="image" src="https://github.com/user-attachments/assets/3517d722-d3a8-4b94-825a-a233b3fd1ecd" />


### Control Flow Guard Nanomites

When CFG protects a call it will emit a:
```c
call [__guard_dispatch_icall_fptr]
```
Where it will load the vtable into rax and then invoke its dispatcher. We hook the dispatcher, then emit a fake stub to a legit protected call address.<br>
This means that if you follow the call it is as if it doesn't even happen.  The hooked CFG Dispatcher will now redirect the code to the real code path. As the attacker follows the fake one. <br>
<img width="375" height="120" alt="image" src="https://github.com/user-attachments/assets/8fa6b672-d4e0-4964-a53c-dc56893c62ef" />
<br>
<img width="465" height="835" alt="image" src="https://github.com/user-attachments/assets/86757832-b5f5-453e-9151-caf92b02b31d" />



## Annotations
```c
__attribute__((annotate("icnano")))
``` 
* Applies instrument callback nanomites to function
```c
__attribute__((annotate("exnano")))
``` 
* Applies exception nanomites to function
```c
__attribute__((annotate("cfgnano")))
``` 
* Applies control flow guard nanomites to function
  
## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
