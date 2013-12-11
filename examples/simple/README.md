Simple Example of STP's C API and using STP as an external CMake project
========================================================================

A developer can use either the **build tree** or **installed** version of STP. By
default the STP build system registers STP with the user's CMake user package
registry when it is built so the build tree version of STP can be used easily
out of the box.

To build this example make sure you have built STP and then in this directory
run:

``` 
$ mkdir bin/ 
$ cd bin/ 
$ cmake-gui ../ 
```

Note you can use ``cmake`` or ``ccmake`` instead of ``cmake-gui``, but I prefer it.

If you use ``cmake-gui``

1. Click the configure button.
2. Select your generator (most people will use UNIX makefiles or Ninja files).
3. Click the finish button.
4. If STP was detected then click on the generate button. If not see the next section.
5. Exit

Now you have succesfully configured you can build and run the simple example:

UNIX Makefiles
--------------

```
$ make
$ ./stp-example
```

Ninja files
-----------

```
$ ninja
$ ./stp-example
```

Detection of STP
================

STP is detected when running CMake to configure the simple example.

If STP is automatically detected then the CMake variable ``STP_DIR`` will be
set to the directory containing the ``STPConfig.cmake`` file. This file exists
in two different locations.

- Root of the build tree.
- Somewhere under the installation directory. For example under UNIX systems if
  the STP installation directory is ``/usr/local/`` then the ``STPConfig.cmake``
  file will probably be installed to ``/usr/local/lib/cmake/STP/``.

A developer can use either location to build against the build or installed
version respectively.

**Warning** there is another file in ``${CMAKE_BINARY_DIR}/CMakeFiles`` with the 
name ``STPConfig.cmake``. **DO NOT USE THIS FILE**

If STP is not detected the developer can set ``STP_DIR`` variable manually and
then reconfigure.  

If things aren't working you should take a look at the CMake documentation on
the ``find_package()`` command in config mode which describes how an external
project like STP will be detected.
