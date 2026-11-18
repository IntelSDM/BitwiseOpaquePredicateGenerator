# Bitwise Opaque Predicate Generator
Built for LLVM 19.1 - Windows x64 <br> <br>

Opaque predicates are without a doubt the most important part of code obfuscation. They allow you to make your code none deterministic by using paths to corrupt/fix up code. <br>
Opaque predicates are why you can't just examine absolutes, as they normal path is likely heavily corrupted without them. <br>
Bitwise equations that are either always true or always false are the simplest version of opaque predicates, a lot of common algorithms such as fermats are pattern scanned. <br>
So we generate our own using out synthesis equipment. To be VERY VERY clear, bitwise equations can be bruteforced in nanoseconds, they aren't secure at all by themselves. <br>
Since they aren't actually secure and a lot of tooling will actually automatically solve them, they become REALLY useful for our tooling, [OpaqueExceptions](https://github.com/IntelSDM/OpaqueExceptionObfuscation) work PERFECTLY with them. <br>
As tooling will auto solve them, they will simply auto solve the wrong path due to the [OpaqueExceptions](https://github.com/IntelSDM/OpaqueExceptionObfuscation); allowing us to turn common tooling such as SMT against the attacker. <br>
Since we have an unlimited supply of equations unlike other implementations, we can chain them with themselves too for more engaging opaque trees. <br>


<img width="1966" height="342" alt="image" src="https://github.com/user-attachments/assets/fff38294-624e-4d30-8b43-45844819571a" /> <br>
<img width="1978" height="512" alt="image" src="https://github.com/user-attachments/assets/7095ca82-f72a-4881-a400-9ffee04989e1" /> <br>
<img width="1977" height="380" alt="image" src="https://github.com/user-attachments/assets/9a6b1e7c-7867-4ff4-9c0d-424a99fc1268" /> <br>
<img width="1963" height="782" alt="image" src="https://github.com/user-attachments/assets/40a97d61-d188-4cf8-a0ad-32ee77ff8ffe" /> <br>

## Annotations
```c
__attribute__((annotate("obfus")))
``` 
* Marks your function for the pass

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
