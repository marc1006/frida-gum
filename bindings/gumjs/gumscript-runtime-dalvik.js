(function () {
    "use strict";

    /*
     * TODO
     *  - JIT... https://github.com/rovo89/Xposed/blob/master/libxposed_dalvik.cpp
     *  - Create Java-source "template"
     *  - Find instance pointer in heap
     *  - Find und handle ```DvmGlobals```
     *  - Rename classes, fields and methods (for deobfuscation)
     */

    /* Reference:
     * - https://www.mulliner.org/android/feed/mulliner_ddi_30c3.pdf
     * - https://www1.informatik.uni-erlangen.de/filepool/publications/Live_Memory_Forensics_on_Android_with_Volatility.pdf

     Load dex files:
     * dexstuff_loaddex()
     * dexstuff_defineclass()

     Important own functions:
     * function proxy(offset, retType, argTypes, wrapper);

     How to get proxy offset:
     * http://osxr.org/android/source/libnativehelper/include/nativehelper/jni.h
     * http://docs.oracle.com/javase/7/docs/technotes/guides/jni/spec/functions.html for the offset

     Methods to use:
     * findClass(...)
     * Usage for Static Fields:
     - PUBLIC: this.getStaticIntField(handle, this.getStaticFieldId(handle, "PUBLIC", "I")),

     Code snippets:
     * Replace classes
     ```args[0].l = “PATH/classes.dex”; // must be a string object 
     cookie = dvm_dalvik_system_DexFile[0](args, &pResult);
     // get class loader
     Method *m = dvmGetCurrentJNIMethod();
     // define class
     u4 args[] = { 
       “org.mulliner.collin.work”, // class name (string object)
       m­>clazz­>classLoader,      // class loader
       cookie                      // use DEX file loaded above  
     };
     dvm_dalvik_system_DexFile[3](args, &pResult);```

     * Example usage
     ```cls = dvmFindLoadedClass(“Ljava/lang/String;”);
     met = dvmFindVirtualMethodHierByDescriptor(cls, “compareTo”,
                                       “(Ljava/lang/String;)I”);```
     * Dump list of loaded classes in current VM
     – Useful to find out which system process runs a specific
     framework service
     ```// level  0 = only class names 1 = class details
     dvmDumpAllClasses(level);
     ```
     * Dump details of specific class: All methods (incl. signature), fields, etc...
     ```cls = dvmFindLoadedClass(“Lorg/mulliner/collin/work”);
     dvmDumpClass(cls, 1);```
     */

    let _runtime = null;
    let _api = null;
    const pointerSize = Process.pointerSize;
    const scratchBuffer = Memory.alloc(pointerSize);
    /* no error */
    const JNI_OK = 0;
    /* generic error */
    const JNI_ERR = -1;
    /* thread detached from the VM */
    const JNI_EDETACHED = -2;
    /* JNI version error */
    const JNI_VERSION = -3;

    const JNI_VERSION_1_6 = 0x00010006;

    const CONSTRUCTOR_METHOD = 1;
    const STATIC_METHOD = 2;
    const INSTANCE_METHOD = 3;

    // fields
    const STATIC_FIELD = 1;
    const INSTANCE_FIELD = 2;

    // android/source/dalvik/vm/Hash.h
    // invalid ptr value
    const HASH_TOMBSTONE = 0xcbcacccd;

    // TODO: 64-bit
    const JNI_ENV_OFFSET_SELF = 12;

    const CLASS_OBJECT_SIZE = 160;
    const CLASS_OBJECT_OFFSET_VTABLE_COUNT = 112;
    const CLASS_OBJECT_OFFSET_VTABLE = 116;

    const OBJECT_OFFSET_CLAZZ = 0;

    const METHOD_SIZE = 56;
    const METHOD_OFFSET_CLAZZ = 0;
    const METHOD_OFFSET_ACCESS_FLAGS = 4;
    const METHOD_OFFSET_METHOD_INDEX = 8;
    const METHOD_OFFSET_REGISTERS_SIZE = 10;
    const METHOD_OFFSET_OUTS_SIZE = 12;
    const METHOD_OFFSET_INS_SIZE = 14;
    const METHOD_OFFSET_INSNS = 32;
    const METHOD_OFFSET_JNI_ARG_INFO = 36;

    Object.defineProperty(this, 'Dalvik', {
        enumerable: true,
        get: function () {
            if (_runtime === null) {
                _runtime = new Runtime();
            }
            return _runtime;
        }
    });

    var Runtime = function Runtime() {
        let api = null;
        let vm = null;
        let classFactory = null;
        let pending = [];

        var initialize = function () {
            api = getApi();
            if (api !== null) {
                vm = new VM(api);
                classFactory = new ClassFactory(api, vm);
            }
        };

        WeakRef.bind(Runtime, function dispose() {
            if (api !== null) {
                vm.perform(function () {
                    var env = vm.getEnv();
                    classFactory.dispose(env);
                    Env.dispose(env);
                });
            }
        });

        Object.defineProperty(this, 'available', {
            enumerable: true,
            get: function () {
                return api !== null;
            }
        });

        this.api = function(){
            return api;
        };

        Object.defineProperty(this, 'getApplicationContext', {
            enumerable: true,
            get: function () {
                var currentApplication = Dalvik.use("android.app.ActivityThread").currentApplication();
                return currentApplication.getApplicationContext();
            }
        });

        Object.defineProperty(this, 'heapSourceBase', {
            enumerable: true,
            get: function () {
                if (!this.available) {
                    throw new Error("Dalvik runtime not available");
                }
                return api.dvmHeapSourceGetBase();
            }
        });

        Object.defineProperty(this, 'heapSourceLimit', {
            enumerable: true,
            get: function () {
                if (!this.available) {
                    throw new Error("Dalvik runtime not available");
                }
                return api.dvmHeapSourceGetLimit();
            }
        });

        function _enumerateLoadedClasses(callbacks, onlyDescription) {
            if (Dalvik.available) {
                const hash_tombstone = 0xcbcacccd;
                const loadedClassesOffset = 172;
                const hashEntrySize = 8;
                const ptrLoadedClassesHashtable = api.gDvm.add(loadedClassesOffset);
                const hashTable = Memory.readPointer(ptrLoadedClassesHashtable);
                const tableSize = Memory.readS32(hashTable);
                const ptrpEntries = hashTable.add(12);
                const pEntries = Memory.readPointer(ptrpEntries);
                const end = tableSize * hashEntrySize;

                for (let offset = 0; offset < end; offset += hashEntrySize) {
                    let pEntriePtr = pEntries.add(offset);
                    let hashValue = Memory.readS32(pEntriePtr);
                    if (hashValue !== 0) {
                        let dataPtr = Memory.readPointer(pEntriePtr.add(4));
                        if (dataPtr !== hash_tombstone) {
                            let descriptionPtr = Memory.readPointer(dataPtr.add(24));
                            let description = Memory.readCString(descriptionPtr);
                            if (onlyDescription) {
                                callbacks.onMatch(description);
                            } else {
                                let objectSize = Memory.readU32(dataPtr.add(56));
                                let sourceFile = Memory.readCString(Memory.readPointer(dataPtr.add(152)));
                                callbacks.onMatch({
                                    pointer: pEntriePtr,
                                    objectSize: objectSize,
                                    sourceFile: sourceFile,
                                    description: description
                                });
                            }
                        }
                    }
                }
                callbacks.onComplete();
            } else {
                throw new Error("Dalvik API not available");
            }
        }

        Object.defineProperty(this, 'enumerateLoadedClassesSync', {
            enumerable: true,
            value: function () {
                if (api !== null) {
                    let classes = [];
                    Dalvik.enumerateLoadedClasses({
                        onMatch: function (c) {
                            classes.push(c);
                        },
                        onComplete: function () {
                        }
                    });
                    return classes;
                } else {
                    throw new Error("Dalvik API not available");
                }
            }
        });

        Object.defineProperty(this, 'enumerateLoadedClasses', {
            enumerable: true,
            value: function(callbacks) {
                _enumerateLoadedClasses(callbacks, true);
            }
        });

        this.perform = function (fn) {
            if (!this.available) {
                throw new Error("Dalvik runtime not available");
            }

            if (classFactory.loader !== null) {
                vm.perform(fn);
            } else {
                pending.push(fn);
                if (pending.length === 1) {
                    vm.perform(function () {
                        var ActivityThread = classFactory.use("android.app.ActivityThread");
                        var Handler = classFactory.use("android.os.Handler");
                        var Looper = classFactory.use("android.os.Looper");

                        var looper = Looper.getMainLooper();
                        var handler = Handler.$new.overload("android.os.Looper").call(Handler, looper);
                        var message = handler.obtainMessage();
                        Handler.dispatchMessage.implementation = function (msg) {
                            var sameHandler = this.$isSameObject(handler);
                            if (sameHandler) {
                                var app = ActivityThread.currentApplication();
                                if (app !== null) {
                                    Handler.dispatchMessage.implementation = null;
                                    var loader = app.getClassLoader();
                                    setTimeout(function () {
                                        classFactory.loader = loader;
                                        pending.forEach(vm.perform, vm);
                                        pending = null;
                                    }, 0);
                                }
                            } else {
                                this.dispatchMessage(msg);
                            }
                        };
                        message.sendToTarget();
                    });
                }
            }
        };

        this.use = function (className) {
            if (classFactory.loader === null) {
                throw new Error("Not allowed outside Dalvik.perform() callback");
            }
            return classFactory.use(className);
        };

        this.cast = function (obj, C) {
            return classFactory.cast(obj, C);
        };

        this.getObjectClassname = function (obj) {
            return classFactory.getObjectClassname(obj);
        };

     
        // Reference: http://stackoverflow.com/questions/2848575/how-to-detect-ui-thread-on-android
        this.isMainThread = function () {
            if (classFactory.loader === null) {
                throw new Error("Not allowed outside Dalvik.perform() callback");
            }
            var Looper = classFactory.use("android.os.Looper");
            var mainLooper = Looper.getMainLooper();
            var myLooper = Looper.myLooper();
            if (myLooper === null) {
                return false;
            }
            return mainLooper.$isSameObject(myLooper);
        };

        // flag: 0 = only class names, 1 = also class details
        this.dumpAllClassesToLogcat = function (flag) {
            if (flag === 0 || flag === 1) {
                api.dvmDumpAllClasses(flag);
                return true;
            } else {
                throw new Error("Flag must be 0 for only class names or 1 for also class details");
            }
        };

        initialize.call(this);
    };

    var ClassFactory = function ClassFactory(api, vm) {
        var factory = this;
        var classes = {};
        var patchedClasses = {};
        var loader = null;

        var initialize = function () {
            api = getApi();
        };

        this.dispose = function (env) {
            for (var entryId in patchedClasses) {
                if (patchedClasses.hasOwnProperty(entryId)) {
                    var entry = patchedClasses[entryId];
                    Memory.writePointer(entry.vtablePtr, entry.vtable);
                    Memory.writeS32(entry.vtableCountPtr, entry.vtableCount);

                    for (var methodId in entry.targetMethods) {
                        if (entry.targetMethods.hasOwnProperty(methodId)) {
                            entry.targetMethods[methodId].implementation = null;
                        }
                    }
                }
            }
            patchedClasses = {};

            for (var classId in classes) {
                if (classes.hasOwnProperty(classId)) {
                    var klass = classes[classId];
                    klass.__methods__.forEach(env.deleteGlobalRef, env);
                    env.deleteGlobalRef(klass.__handle__);
                }
            }
            classes = {};
        };

        Object.defineProperty(this, 'loader', {
            enumerable: true,
            get: function () {
                return loader;
            },
            set: function (value) {
                loader = value;
            }
        });

        this.use = function (className) {
            let C = classes[className];
            if (!C) {
                let env = vm.getEnv();
                if (loader !== null) {
                    let klassObj = loader.loadClass(className);
                    C = ensureClass(klassObj.$handle, className);
                } else {
                    let handle = env.findClass(className.replace(/\./g, "/"));
                    try {
                        C = ensureClass(handle, className);
                    } finally {
                        env.deleteLocalRef(handle);
                    }
                }
            }
            return new C(C.__handle__, null);
        };

        this.cast = function (obj, klass) {
            var handle = obj.hasOwnProperty('$handle') ? obj.$handle : obj;
            var C = klass.$classWrapper;
            return new C(C.__handle__, handle);
        };

        this.getObjectClassname = function (obj) {
            if (obj instanceof NativePointer) {
                var env = vm.getEnv();
                var jklass = env.getObjectClass(obj);
                var invokeObjectMethodNoArgs = env.method('pointer', []);

                var stringObj = invokeObjectMethodNoArgs(env.handle, jklass, env.javaLangClass().getName);
                var clsStr = env.stringFromJni(stringObj);
                /*
                 // first get the class object
                 var classObj = invokeObjectMethodNoArgs(env.handle, jklass, env.javaLangObject().getClass);

                 // now get the descriptor of it
                 var cls = env.getObjectClass(classObj);
                 var stringObj = invokeObjectMethodNoArgs(env.handle, cls, env.javaLangClass().getName);
                 var clsStr = env.stringFromJni(stringObj);
                 env.deleteLocalRef(classObj);
                 env.deleteLocalRef(cls);
                 */
                env.deleteLocalRef(jklass);
                env.deleteLocalRef(stringObj);
                //this.deleteLocalRef(throwable);
                return clsStr;
            } else {
                throw new Error('Parameter has to be an native pointer.');
            }
        };

        var ensureClass = function (classHandle, cachedName) {
            let env = vm.getEnv();

            let name = cachedName !== null ? cachedName : env.getClassName(classHandle);
            let klass = classes[name];
            if (klass) {
                return klass;
            }

            let superHandle = env.getSuperclass(classHandle);
            let superKlass;
            if (!superHandle.isNull()) {
                superKlass = ensureClass(superHandle, null);
                env.deleteLocalRef(superHandle);
            } else {
                superKlass = null;
            }

            eval("klass = function " + basename(name) + "(classHandle, handle) {" +
                "var env = vm.getEnv();" +
                "this.$classWrapper = klass;" +
                "this.$classHandle = env.newGlobalRef(classHandle);" +
                "this.$handle = (handle !== null) ? env.newGlobalRef(handle) : null;" +
                "this.$weakRef = WeakRef.bind(this, makeHandleDestructor(this.$handle, this.$classHandle));" +
                "};");

            classes[name] = klass;

            function initializeClass() {
                klass.__name__ = name;
                klass.__handle__ = env.newGlobalRef(classHandle);
                klass.__methods__ = [];
                klass.__fields__ = [];

                let ctor = null;
                Object.defineProperty(klass.prototype, "$new", {
                    get: function () {
                        if (ctor === null) {
                            vm.perform(function () {
                                ctor = makeConstructor(klass.__handle__, vm.getEnv());
                            });
                        }
                        return ctor;
                    }
                });
                klass.prototype.$dispose = dispose;

                klass.prototype.$isSameObject = function (obj) {
                    var env = vm.getEnv();
                    return env.isSameObject(obj.$handle, this.$handle);
                };

                Object.defineProperty(klass.prototype, 'class', {
                    get: function () {
                        var Clazz = factory.use("java.lang.Class");
                        return factory.cast(this.$classHandle, Clazz);
                    }
                });

                addMethods();
                addFields();
            }

            var dispose = function () {
                WeakRef.unbind(this.$weakRef);
            };

            var makeConstructor = function (classHandle, env) {
                var Constructor = env.javaLangReflectConstructor();
                var invokeObjectMethodNoArgs = env.method('pointer', []);

                var jsMethods = [];
                var jsRetType = objectType(name, false);
                var constructors = invokeObjectMethodNoArgs(env.handle, classHandle, env.javaLangClass().getDeclaredConstructors);
                var numConstructors = env.getArrayLength(constructors);
                for (var constructorIndex = 0; constructorIndex !== numConstructors; constructorIndex++) {
                    var constructor = env.getObjectArrayElement(constructors, constructorIndex);

                    var methodId = env.fromReflectedMethod(constructor);
                    var jsArgTypes = [];

                    var types = invokeObjectMethodNoArgs(env.handle, constructor, Constructor.getGenericParameterTypes);
                    env.deleteLocalRef(constructor);
                    var numTypes = env.getArrayLength(types);
                    try {
                        for (var typeIndex = 0; typeIndex !== numTypes; typeIndex++) {
                            var t = env.getObjectArrayElement(types, typeIndex);
                            try {
                                var argType = typeFromClassName(env.getTypeName(t));
                                jsArgTypes.push(argType);
                            } finally {
                                env.deleteLocalRef(t);
                            }
                        }
                    } catch (e) {
                        continue;
                    } finally {
                        env.deleteLocalRef(types);
                    }

                    jsMethods.push(makeMethod(CONSTRUCTOR_METHOD, methodId, jsRetType, jsArgTypes, env));
                }
                env.deleteLocalRef(constructors);

                if (jsMethods.length === 0)
                    throw new Error("no supported overloads");

                return makeMethodDispatcher("<init>", jsMethods);
            };

            var addFields = function () {
                let invokeObjectMethodNoArgs = env.method('pointer', []);
                let Field_getName = env.javaLangReflectField().getName;

                let fieldHandles = klass.__fields__;
                let jsFields = {};

                var fields = invokeObjectMethodNoArgs(env.handle, classHandle, env.javaLangClass().getDeclaredFields);
                var numFields = env.getArrayLength(fields);
                for (let fieldIndex = 0; fieldIndex !== numFields; fieldIndex++) {
                    let field = env.getObjectArrayElement(fields, fieldIndex);
                    let name = invokeObjectMethodNoArgs(env.handle, field, Field_getName);
                    let jsName = env.stringFromJni(name);
                    env.deleteLocalRef(name);
                    let fieldHandle = env.newGlobalRef(field);
                    fieldHandles.push(fieldHandle);
                    env.deleteLocalRef(field);

                    jsFields[jsName] = fieldHandle;
                }

                // define access to the fields in the class (klass)
                Object.keys(jsFields).forEach(function (name) {
                    var m = null;
                    Object.defineProperty(klass.prototype, name, {
                        configurable: true,
                        get: function () {
                            if (m === null) {
                                vm.perform(function () {
                                    m = makeField(name, jsFields[name], vm.getEnv());
                                });
                            }
                            // TODO for the moment it's an ugly bugfix...
                            m.temp = this;

                            return m;
                        }
                    });
                });
            };

            let makeField = function (name, handle, env) {
                let Field = env.javaLangReflectField();
                let Modifier = env.javaLangReflectModifier();
                let invokeObjectMethodNoArgs = env.method('pointer', []);
                let invokeIntMethodNoArgs = env.method('int32', []);
                let invokeUInt8MethodNoArgs = env.method('uint8', []);

                let fieldId = env.fromReflectedField(handle);
                let fieldType = invokeObjectMethodNoArgs(env.handle, handle, Field.getGenericType);
                let modifiers = invokeIntMethodNoArgs(env.handle, handle, Field.getModifiers);

                // TODO there should be the opportunity to see the modifiers
                let jsType = (modifiers & Modifier.STATIC) !== 0 ? STATIC_FIELD : INSTANCE_FIELD;

                let jsFieldType;

                try {
                    jsFieldType = typeFromClassName(env.getTypeName(fieldType));
                } catch (e) {
                    return null;
                } finally {
                    env.deleteLocalRef(fieldType);
                }

                var field = createField(jsType, fieldId, jsFieldType, env);

                if (field === null)
                    throw new Error("No supported field");

                return field;
            };

            var createField = function (type, fieldId, fieldType, env) {
                var targetFieldId = fieldId;
                var originalFieldId = null;

                var rawFieldType = fieldType.type;
                var invokeTarget = null;
                if (type === STATIC_FIELD) {
                    invokeTarget = env.staticField(rawFieldType);
                } else if (type === INSTANCE_FIELD) {

                    invokeTarget = env.field(rawFieldType);
                } else {
                    throw new Error("Should not be the case");
                }

                var frameCapacity = 2;
                var callArgs = [
                    "env.handle",
                    type === INSTANCE_FIELD ? "this.$handle" : "this.$classHandle",
                    "targetFieldId"
                ];

                var returnCapture, returnStatements;
                if (rawFieldType === 'void') {
                    throw new Error("Should not be the case");
                }

                if (fieldType.fromJni) {
                    frameCapacity++;
                    returnCapture = "var rawResult = ";
                    returnStatements = "var result = fieldType.fromJni.call(this, rawResult, env);" +
                        "env.popLocalFrame(NULL);" +
                        "return result;";
                } else {
                    returnCapture = "var result = ";
                    returnStatements = "env.popLocalFrame(NULL);" +
                        "return result;";
                }

                let fu;
                eval("fu = function () {" +
                    "var isInstance = this.$handle !== null;" +
                    "if (type === INSTANCE_FIELD && isInstance === false) { " +
                    "throw new Error(name + ': cannot get instance field without an instance');" +
                    "}" +
                    "var env = vm.getEnv();" +
                    "if (env.pushLocalFrame(" + frameCapacity + ") !== JNI_OK) {" +
                    "env.exceptionClear();" +
                    "throw new Error(\"Out of memory\");" +
                    "}" +
                    "try {" +
                    "synchronizeVtable.call(this, env, type === INSTANCE_FIELD);" +
                    returnCapture + "invokeTarget(" + callArgs.join(", ") + ");" +
                    "} catch (e) {" +
                    "env.popLocalFrame(NULL);" +
                    "throw e;" +
                    "}" +
                    "var throwable = env.exceptionOccurred();" +
                    "if (!throwable.isNull()) {" +
                    "env.exceptionClear();" +
                    "var description = env.method('pointer', [])(env.handle, throwable, env.javaLangObject().toString);" +
                    "var descriptionStr = env.stringFromJni(description);" +
                    "env.popLocalFrame(NULL);" +
                    "throw new Error(descriptionStr);" +
                    "}" +
                    returnStatements +
                    "}");

                /*
                 * setter
                 */
                var setFunction = null;
                if (type === STATIC_FIELD) {
                    setFunction = env.setStaticField(rawFieldType);
                } else if (type === INSTANCE_FIELD) {
                    setFunction = env.setField(rawFieldType);
                } else {
                    throw new Error("Should not be the case");
                }

                var inputStatement = null;
                if (fieldType.toJni) {
                    inputStatement = "var input = fieldType.toJni.call(this, valu, env);";
                } else {
                    inputStatement = "var input = valu;";
                    //   throw new Error('unable to convert to JNI ' + fieldType);
                }

                let mu;
                eval("mu = function (valu) {" +
                    "var isInstance = this.$handle !== null;" +
                    "if (type === INSTANCE_FIELD && isInstance === false) { " +
                    "throw new Error(name + ': cannot set an instance field without an instance');" +
                    "}" +
                    "if (!fieldType.isCompatible(valu)) {throw new Error(name + ': input is not compatible');}" +
                    "var env = vm.getEnv();" +
                    "try {" +
                    inputStatement +
                    "setFunction(" + callArgs.join(", ") + ", input);" +
                    "} catch (e) {" +
                    "throw e;" +
                    "}" +
                    "var throwable = env.exceptionOccurred();" +
                    "if (!throwable.isNull()) {" +
                    "env.exceptionClear();" +
                    "var description = env.method('pointer', [])(env.handle, throwable, env.javaLangObject().toString);" +
                    "var descriptionStr = env.stringFromJni(description);" +
                    "env.popLocalFrame(NULL);" +
                    "throw new Error(descriptionStr);" +
                    "}" +
                    "}");

                var f = {};
                Object.defineProperty(f, "value", {
                    enumerable: true,
                    get: function () {
                        return fu.call(this.temp);
                    },
                    set: function (val) {
                        mu.call(this.temp, val);
                    }
                });

                Object.defineProperty(f, 'holder', {
                    enumerable: true,
                    value: klass
                });

                Object.defineProperty(f, 'type', {
                    enumerable: true,
                    value: type
                });

                Object.defineProperty(f, 'fieldType', {
                    enumerable: true,
                    value: fieldType
                });

                var implementation = null;
                var synchronizeVtable = function (env) {
                    return;
                };

                return f;
            };

            var addMethods = function () {
                let invokeObjectMethodNoArgs = env.method('pointer', []);
                let Method_getName = env.javaLangReflectMethod().getName;

                let methodHandles = klass.__methods__;
                let jsMethods = {};

                let methods = invokeObjectMethodNoArgs(env.handle, classHandle, env.javaLangClass().getDeclaredMethods);
                let numMethods = env.getArrayLength(methods);
                for (var methodIndex = 0; methodIndex !== numMethods; methodIndex++) {
                    var method = env.getObjectArrayElement(methods, methodIndex);
                    var name = invokeObjectMethodNoArgs(env.handle, method, Method_getName);
                    var jsName = env.stringFromJni(name);
                    env.deleteLocalRef(name);
                    var methodHandle = env.newGlobalRef(method);
                    methodHandles.push(methodHandle);
                    env.deleteLocalRef(method);

                    var jsOverloads;
                    if (jsMethods.hasOwnProperty(jsName)) {
                        jsOverloads = jsMethods[jsName];
                    } else {
                        jsOverloads = [];
                        jsMethods[jsName] = jsOverloads;
                    }
                    jsOverloads.push(methodHandle);
                }

                Object.keys(jsMethods).forEach(function (name) {
                    var m = null;
                    Object.defineProperty(klass.prototype, name, {
                        configurable: true,
                        get: function () {
                            if (m === null) {
                                vm.perform(function () {
                                    m = makeMethodFromOverloads(name, jsMethods[name], vm.getEnv());
                                });
                            }
                            return m;
                        }
                    });
                });
            };

            var makeMethodFromOverloads = function (name, overloads, env) {
                var Method = env.javaLangReflectMethod();
                var Modifier = env.javaLangReflectModifier();
                var invokeObjectMethodNoArgs = env.method('pointer', []);
                var invokeIntMethodNoArgs = env.method('int32', []);
                var invokeUInt8MethodNoArgs = env.method('uint8', []);

                var methods = overloads.map(function (handle) {
                    var methodId = env.fromReflectedMethod(handle);
                    var retType = invokeObjectMethodNoArgs(env.handle, handle, Method.getGenericReturnType);
                    var argTypes = invokeObjectMethodNoArgs(env.handle, handle, Method.getGenericParameterTypes);
                    var modifiers = invokeIntMethodNoArgs(env.handle, handle, Method.getModifiers);
                    var isVarArgs = invokeUInt8MethodNoArgs(env.handle, handle, Method.isVarArgs) ? true : false;

                    var jsType = (modifiers & Modifier.STATIC) !== 0 ? STATIC_METHOD : INSTANCE_METHOD;

                    var jsRetType;
                    var jsArgTypes = [];

                    try {
                        jsRetType = typeFromClassName(env.getTypeName(retType));
                    } catch (e) {
                        env.deleteLocalRef(argTypes);
                        return null;
                    } finally {
                        env.deleteLocalRef(retType);
                    }

                    try {
                        var numArgTypes = env.getArrayLength(argTypes);
                        for (var argTypeIndex = 0; argTypeIndex !== numArgTypes; argTypeIndex++) {
                            var t = env.getObjectArrayElement(argTypes, argTypeIndex);
                            try {
                                var argClassName = (isVarArgs && argTypeIndex === numArgTypes - 1) ? env.getArrayTypeName(t) : env.getTypeName(t);
                                var argType = typeFromClassName(argClassName);
                                jsArgTypes.push(argType);
                            } finally {
                                env.deleteLocalRef(t);
                            }
                        }
                    } catch (e) {
                        return null;
                    } finally {
                        env.deleteLocalRef(argTypes);
                    }

                    return makeMethod(jsType, methodId, jsRetType, jsArgTypes, env);
                }).filter(function (m) {
                    return m !== null;
                });

                if (methods.length === 0)
                    throw new Error("no supported overloads");

                if (name === "valueOf") {
                    var hasDefaultValueOf = methods.some(function implementsDefaultValueOf(m) {
                        return m.type === INSTANCE_METHOD && m.argumentTypes.length === 0;
                    });
                    if (!hasDefaultValueOf) {
                        var defaultValueOf = function defaultValueOf() {
                            return this;
                        };

                        Object.defineProperty(defaultValueOf, 'holder', {
                            enumerable: true,
                            value: klass
                        });

                        Object.defineProperty(defaultValueOf, 'type', {
                            enumerable: true,
                            value: INSTANCE_METHOD
                        });

                        Object.defineProperty(defaultValueOf, 'returnType', {
                            enumerable: true,
                            value: typeFromClassName('int')
                        });

                        Object.defineProperty(defaultValueOf, 'argumentTypes', {
                            enumerable: true,
                            value: []
                        });

                        Object.defineProperty(defaultValueOf, 'canInvokeWith', {
                            enumerable: true,
                            value: function (args) {
                                return args.length === 0;
                            }
                        });

                        methods.push(defaultValueOf);
                    }
                }

                return makeMethodDispatcher(name, methods);
            };

            var makeMethodDispatcher = function (name, methods) {
                var candidates = {};
                methods.forEach(function (m) {
                    var numArgs = m.argumentTypes.length;
                    var group = candidates[numArgs];
                    if (!group) {
                        group = [];
                        candidates[numArgs] = group;
                    }
                    group.push(m);
                });

                var f = function () {
                    var isInstance = this.$handle !== null;
                    if (methods[0].type !== INSTANCE_METHOD && isInstance) {
                        throw new Error(name + ": cannot call static method by way of an instance");
                    } else if (methods[0].type === INSTANCE_METHOD && !isInstance) {
                        if (name === 'toString') {
                            return "<" + this.$classWrapper.__name__ + ">";
                        }
                        throw new Error(name + ": cannot call instance method without an instance");
                    }
                    var group = candidates[arguments.length];
                    if (!group) {
                        throw new Error(name + ": argument count does not match any overload");
                    }
                    for (var i = 0; i !== group.length; i++) {
                        var method = group[i];
                        if (method.canInvokeWith(arguments)) {
                            return method.apply(this, arguments);
                        }
                    }
                    throw new Error(name + ": argument types do not match any overload");
                };

                Object.defineProperty(f, 'overloads', {
                    enumerable: true,
                    value: methods
                });

                Object.defineProperty(f, 'overload', {
                    enumerable: true,
                    value: function () {
                        var group = candidates[arguments.length];
                        if (!group) {
                            throw new Error(name + ": argument count does not match any overload");
                        }

                        var signature = Array.prototype.join.call(arguments, ":");
                        for (var i = 0; i !== group.length; i++) {
                            var method = group[i];
                            var s = method.argumentTypes.map(function (t) {
                                return t.className;
                            }).join(":");
                            if (s === signature) {
                                return method;
                            }
                        }
                        throw new Error(name + ": specified argument types do not match any overload");
                    }
                });

                Object.defineProperty(f, 'holder', {
                    enumerable: true,
                    get: methods[0].holder
                });

                Object.defineProperty(f, 'type', {
                    enumerable: true,
                    value: methods[0].type
                });

                if (methods.length === 1) {
                    Object.defineProperty(f, 'implementation', {
                        enumerable: true,
                        get: function () {
                            return methods[0].implementation;
                        },
                        set: function (imp) {
                            methods[0].implementation = imp;
                        }
                    });

                    Object.defineProperty(f, 'returnType', {
                        enumerable: true,
                        value: methods[0].returnType
                    });

                    Object.defineProperty(f, 'argumentTypes', {
                        enumerable: true,
                        value: methods[0].argumentTypes
                    });

                    Object.defineProperty(f, 'canInvokeWith', {
                        enumerable: true,
                        value: methods[0].canInvokeWith
                    });
                } else {
                    var throwAmbiguousError = function () {
                        throw new Error("Method has more than one overload. Please resolve by for example: `method.overload('int')`");
                    };

                    Object.defineProperty(f, 'implementation', {
                        enumerable: true,
                        get: throwAmbiguousError,
                        set: throwAmbiguousError
                    });

                    Object.defineProperty(f, 'returnType', {
                        enumerable: true,
                        get: throwAmbiguousError
                    });

                    Object.defineProperty(f, 'argumentTypes', {
                        enumerable: true,
                        get: throwAmbiguousError
                    });

                    Object.defineProperty(f, 'canInvokeWith', {
                        enumerable: true,
                        get: throwAmbiguousError
                    });
                }

                return f;
            };

            var makeMethod = function (type, methodId, retType, argTypes, env) {
                var targetMethodId = methodId;
                var originalMethodId = null;

                var rawRetType = retType.type;
                var rawArgTypes = argTypes.map(function (t) {
                    return t.type;
                });
                var invokeTarget;
                if (type == CONSTRUCTOR_METHOD) {
                    invokeTarget = env.constructor(rawArgTypes);
                } else if (type == STATIC_METHOD) {
                    invokeTarget = env.staticMethod(rawRetType, rawArgTypes);
                } else if (type == INSTANCE_METHOD) {
                    invokeTarget = env.method(rawRetType, rawArgTypes);
                }

                var frameCapacity = 2;
                var argVariableNames = argTypes.map(function (t, i) {
                    return "a" + (i + 1);
                });
                var callArgs = [
                    "env.handle",
                    type === INSTANCE_METHOD ? "this.$handle" : "this.$classHandle",
                    "targetMethodId"
                ].concat(argTypes.map(function (t, i) {
                        if (t.toJni) {
                            frameCapacity++;
                            return "argTypes[" + i + "].toJni.call(this, " + argVariableNames[i] + ", env)";
                        }
                        return argVariableNames[i];
                    }));
                var returnCapture, returnStatements;
                if (rawRetType === 'void') {
                    returnCapture = "";
                    returnStatements = "env.popLocalFrame(NULL);";
                } else {
                    if (retType.fromJni) {
                        frameCapacity++;
                        returnCapture = "var rawResult = ";
                        returnStatements = "var result = retType.fromJni.call(this, rawResult, env);" +
                            "env.popLocalFrame(NULL);" +
                            "return result;";
                    } else {
                        returnCapture = "var result = ";
                        returnStatements = "env.popLocalFrame(NULL);" +
                            "return result;";
                    }
                }

                let f;
                eval("f = function (" + argVariableNames.join(", ") + ") {" +
                    "var env = vm.getEnv();" +
                    "if (env.pushLocalFrame(" + frameCapacity + ") !== JNI_OK) {" +
                    "env.exceptionClear();" +
                    "throw new Error(\"Out of memory\");" +
                    "}" +
                    "try {" +
                    "synchronizeVtable.call(this, env, type === INSTANCE_METHOD);" +
                    returnCapture + "invokeTarget(" + callArgs.join(", ") + ");" +
                    "} catch (e) {" +
                    "env.popLocalFrame(NULL);" +
                    "throw e;" +
                    "}" +
                    "var throwable = env.exceptionOccurred();" +
                    "if (!throwable.isNull()) {" +
                    "env.exceptionClear();" +
                    "var description = env.method('pointer', [])(env.handle, throwable, env.javaLangObject().toString);" +
                    "var descriptionStr = env.stringFromJni(description);" +
                    "env.popLocalFrame(NULL);" +
                    "throw new Error(descriptionStr);" +
                    "}" +
                    returnStatements +
                    "}");

                Object.defineProperty(f, 'holder', {
                    enumerable: true,
                    value: klass
                });

                Object.defineProperty(f, 'type', {
                    enumerable: true,
                    value: type
                });

                var implementation = null;
                var synchronizeVtable = function (env, instance) {
                    if (originalMethodId === null) {
                        return; // nothing to do – implementation hasn't been replaced
                    }

                    var thread = Memory.readPointer(env.handle.add(JNI_ENV_OFFSET_SELF));
                    /*
                    var objectPtr = api.dvmDecodeIndirectRef(thread, this.$handle);
                    var classObject = Memory.readPointer(objectPtr.add(OBJECT_OFFSET_CLAZZ));
                    */
                    var objectPtr = api.dvmDecodeIndirectRef(thread, instance? this.$handle: this.$classHandle);
                    let classObject;
                    if (instance) {
                        classObject = Memory.readPointer(objectPtr.add(OBJECT_OFFSET_CLAZZ));
                    } else {
                        classObject = objectPtr; //Memory.readPointer(objectPtr);
                    }
                    var key = classObject.toString(16);
                    var entry = patchedClasses[key];
                    if (!entry) {
                        var vtablePtr = classObject.add(CLASS_OBJECT_OFFSET_VTABLE);
                        var vtableCountPtr = classObject.add(CLASS_OBJECT_OFFSET_VTABLE_COUNT);
                        var vtable = Memory.readPointer(vtablePtr);
                        var vtableCount = Memory.readS32(vtableCountPtr);

                        var vtableSize = vtableCount * pointerSize;
                        var shadowVtable = Memory.alloc(2 * vtableSize);
                        Memory.copy(shadowVtable, vtable, vtableSize);
                        Memory.writePointer(vtablePtr, shadowVtable);

                        entry = {
                            classObject: classObject,
                            vtablePtr: vtablePtr,
                            vtableCountPtr: vtableCountPtr,
                            vtable: vtable,
                            vtableCount: vtableCount,
                            shadowVtable: shadowVtable,
                            shadowVtableCount: vtableCount,
                            targetMethods: {}
                        };
                        patchedClasses[key] = entry;
                    }

                    key = methodId.toString(16);
                    var method = entry.targetMethods[key];
                    if (!method) {
                        var methodIndex = entry.shadowVtableCount++;
                        Memory.writePointer(entry.shadowVtable.add(methodIndex * pointerSize), targetMethodId);
                        Memory.writeU16(targetMethodId.add(METHOD_OFFSET_METHOD_INDEX), methodIndex);
                        Memory.writeS32(entry.vtableCountPtr, entry.shadowVtableCount);

                        entry.targetMethods[key] = f;
                    }
                };
                Object.defineProperty(f, 'implementation', {
                    enumerable: true,
                    get: function () {
                        return implementation;
                    },
                    set: function (fn) {
                        if (fn === null && originalMethodId === null) {
                            return;
                        }

                        if (originalMethodId === null) {
                            originalMethodId = Memory.dup(methodId, METHOD_SIZE);
                            targetMethodId = Memory.dup(methodId, METHOD_SIZE);
                        }

                        if (fn !== null) {
                            implementation = implement(f, fn);

                            var argsSize = argTypes.reduce(function (acc, t) {
                                return acc + t.size;
                            }, 0);
                            if (type === INSTANCE_METHOD) {
                                argsSize++;
                            }

                            /* make method native (with 0x0100)
                             * insSize and registersSize are set to arguments size
                             */
                            var accessFlags = Memory.readU32(methodId.add(METHOD_OFFSET_ACCESS_FLAGS)) | 0x0100;
                            var registersSize = argsSize;

                            var outsSize = 0;
                            var insSize = argsSize;
                            // parse method arguments
                            var jniArgInfo = 0x80000000;


                            Memory.writeU32(methodId.add(METHOD_OFFSET_ACCESS_FLAGS), accessFlags);
                            Memory.writeU16(methodId.add(METHOD_OFFSET_REGISTERS_SIZE), registersSize);
                            Memory.writeU16(methodId.add(METHOD_OFFSET_OUTS_SIZE), outsSize);
                            Memory.writeU16(methodId.add(METHOD_OFFSET_INS_SIZE), insSize);
                            Memory.writeU32(methodId.add(METHOD_OFFSET_JNI_ARG_INFO), jniArgInfo);

                            api.dvmUseJNIBridge(methodId, implementation);
                        } else {
                            Memory.copy(methodId, originalMethodId, METHOD_SIZE);
                        }
                    }
                });

                Object.defineProperty(f, 'returnType', {
                    enumerable: true,
                    value: retType
                });

                Object.defineProperty(f, 'argumentTypes', {
                    enumerable: true,
                    value: argTypes
                });

                Object.defineProperty(f, 'canInvokeWith', {
                    enumerable: true,
                    value: function (args) {
                        if (args.length !== argTypes.length) {
                            return false;
                        }

                        return argTypes.every(function (t, i) {
                            return t.isCompatible(args[i]);
                        });
                    }
                });

                return f;
            };

            if (superKlass !== null) {
                var Surrogate = function () {
                    this.constructor = klass;
                };
                Surrogate.prototype = superKlass.prototype;
                klass.prototype = new Surrogate();

                klass.__super__ = superKlass.prototype;
            } else {
                klass.__super__ = null;
            }

            initializeClass();

            // Guard against use-after-"free"
            classHandle = null;
            env = null;

            return klass;
        };

        var makeHandleDestructor = function () {
            var handles = Array.prototype.slice.call(arguments).filter(function (h) {
                return h !== null;
            });
            return function () {
                vm.perform(function () {
                    var env = vm.getEnv();
                    handles.forEach(env.deleteGlobalRef, env);
                });
            };
        };

        var implement = function (method, fn) {
            var env = vm.getEnv();

            if (method.hasOwnProperty('overloads')) {
                if (method.overloads.length > 1) {
                    throw new Error("Method has more than one overload. Please resolve by for example: `method.overload('int')`");
                }
                method = method.overloads[0];
            }

            var C = method.holder;
            var type = method.type;
            var retType = method.returnType;
            var argTypes = method.argumentTypes;
            var rawRetType = retType.type;
            var rawArgTypes = argTypes.map(function (t) {
                return t.type;
            });

            var frameCapacity = 2;
            var argVariableNames = argTypes.map(function (t, i) {
                return "a" + (i + 1);
            });
            let callArgs = argTypes.map(function (t, i) {
                if (t.fromJni) {
                    frameCapacity++;
                    return "argTypes[" + i + "].fromJni.call(self, " + argVariableNames[i] + ", env)";
                }
                return argVariableNames[i];
            });
            let returnCapture, returnStatements, returnNothing;
            if (rawRetType === 'void') {
                returnCapture = "";
                returnStatements = "env.popLocalFrame(NULL);";
                returnNothing = "return;";
            } else {
                if (retType.toJni) {
                    frameCapacity++;
                    returnCapture = "var result = ";
                    if (retType.type === 'pointer') {
                        returnStatements = "var rawResult = retType.toJni.call(this, result, env);" +
                            "return env.popLocalFrame(rawResult);";
                        returnNothing = "return NULL;";
                    } else {
                        returnStatements = "var rawResult = retType.toJni.call(this, result, env);" +
                            "env.popLocalFrame(NULL);" +
                            "return rawResult;";
                        returnNothing = "return 0;";
                    }
                } else {
                    returnCapture = "var result = ";
                    returnStatements = "env.popLocalFrame(NULL);" +
                        "return result;";
                    returnNothing = "return 0;";
                }
            }
            let f;
            eval("f = function (" + ["envHandle", "thisHandle"].concat(argVariableNames).join(", ") + ") {" +
                "var env = new Env(envHandle);" +
                "if (env.pushLocalFrame(" + frameCapacity + ") !== JNI_OK) {" +
                    "return;" +
                "}" +
                ((type === INSTANCE_METHOD) ? "var self = new C(C.__handle__, thisHandle);" : "var self = new C(thisHandle, null);") +
                "try {" +
                    returnCapture + "fn.call(" + ["self"].concat(callArgs).join(", ") + ");" +
                "} catch (e) {" +
                    "if (typeof e === 'object' && e.hasOwnProperty('$handle')) {" +
                        "env.throw(e.$handle);" +
                        returnNothing +
                    "} else {" +
                        "throw e;" +
                    "}" +
                "}" +
                returnStatements +
            "}");

            Object.defineProperty(f, 'type', {
                enumerable: true,
                value: type
            });

            Object.defineProperty(f, 'returnType', {
                enumerable: true,
                value: retType
            });

            Object.defineProperty(f, 'argumentTypes', {
                enumerable: true,
                value: argTypes
            });

            Object.defineProperty(f, 'canInvokeWith', {
                enumerable: true,
                value: function (args) {
                    if (args.length !== argTypes.length) {
                        return false;
                    }

                    return argTypes.every(function (t, i) {
                        return t.isCompatible(args[i]);
                    });
                }
            });

            return new NativeCallback(f, rawRetType, ['pointer', 'pointer'].concat(rawArgTypes));
        };

        var typeFromClassName = function (className) {
            var type = types[className];
            if (!type) {
                if (className.indexOf("[") === 0) {
                    type = arrayType(className.substring(1));
                } else {
                    type = objectType(className, true);
                }
            }

            var result = {
                className: className
            };
            for (var key in type) {
                if (type.hasOwnProperty(key)) {
                    result[key] = type[key];
                }
            }
            return result;
        };

        /*
         * http://docs.oracle.com/javase/6/docs/technotes/guides/jni/spec/types.html#wp9502
         * http://www.liaohuqiu.net/posts/android-object-size-dalvik/
         */
        var types = {
            'boolean': {
                type: 'uint8',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'boolean';
                },
                fromJni: function (v) {
                    return v ? true : false;
                },
                toJni: function (v) {
                    return v ? 1 : 0;
                }
            },
            'byte': {
                type: 'int8',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'number';
                }
            },
            'char': {
                type: 'uint16',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'string' && v.length === 1;
                },
                fromJni: function (c) {
                    return String.fromCharCode(c);
                },
                toJni: function (s) {
                    return s.charCodeAt(0);
                }
            },
            'short': {
                type: 'int16',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'number';
                }
            },
            'int': {
                type: 'int32',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'number';
                }
            },
            'long': {
                type: 'int64',
                size: 2,
                isCompatible: function (v) {
                    return typeof v === 'number';
                }
            },
            'float': {
                type: 'float',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'number';
                }
            },
            'double': {
                type: 'double',
                size: 2,
                isCompatible: function (v) {
                    return typeof v === 'number';
                }
            },
            'void': {
                type: 'void',
                size: 0,
                isCompatible: function () {
                    return false;
                }
            },
            '[B': {
                type: 'pointer',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'object' && v.hasOwnProperty('length');
                },
                fromJni: function () {
                    throw new Error("Not yet implemented ([B)");
                },
                toJni: function () {
                    throw new Error("Not yet implemented ([B)");
                }
            },
            '[C': {
                type: 'pointer',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'object' && v.hasOwnProperty('length');
                },
                fromJni: function () {
                    throw new Error("Not yet implemented ([C)");
                },
                toJni: function () {
                    throw new Error("Not yet implemented ([C)");
                }
            },
            '[I': {
                type: 'pointer',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'object' && v.hasOwnProperty('length');
                },
                fromJni: function () {
                    throw new Error("Not yet implemented ([I)");
                },
                toJni: function () {
                    throw new Error("Not yet implemented ([I)");
                }
            },
            // TODO should it not be '[Ljava/lang/String;'?
            '[Ljava.lang.String;': {
                type: 'pointer',
                size: 1,
                isCompatible: function (v) {
                    return typeof v === 'object' && v.hasOwnProperty('length') && (v.length === 0 || typeof v[0] === 'string');
                },
                fromJni: function (h, env) {
                    var result = [];
                    var length = env.getArrayLength(h);
                    for (var i = 0; i !== length; i++) {
                        var s = env.getObjectArrayElement(h, i);
                        result.push(env.stringFromJni(s));
                        env.deleteLocalRef(s);
                    }
                    return result;
                },
                toJni: function (strings, env) {
                    // TODO check javaLangString...
                    var result = env.newObjectArray(strings.length, env.javaLangString().handle, NULL);
                    for (var i = 0; i !== strings.length; i++) {
                        var s = env.newStringUtf(strings[i]);
                        env.setObjectArrayElement(result, i, s);
                        env.deleteLocalRef(s);
                    }
                    return result;
                }
            }
        };

        var objectType = function (className, unbox) {
            return {
                type: 'pointer',
                size: 1,
                isCompatible: function (v) {
                    if (className === 'java.lang.String' && typeof v === 'string') {
                        return true;
                    }

                    return typeof v === 'object' && v.hasOwnProperty('$handle'); // TODO: improve strictness
                },
                fromJni: function (h, env) {
                    if (h.isNull()) {
                        return null;
                    } else if (className === 'java.lang.String' && unbox) {
                        return env.stringFromJni(h);
                    } else if (this.$handle !== null && env.isSameObject(h, this.$handle)) {
                        return this;
                    } else {
                        return factory.cast(h, factory.use(className));
                    }
                },
                toJni: function (o, env) {
                    if (typeof o === 'string') {
                        return env.newStringUtf(o);
                    }

                    return o.$handle;
                }
            };
        };

        var arrayType = function (rawElementClassName) {
            var elementClassName;
            var isPrimitive;
            if (rawElementClassName[0] === "L" && rawElementClassName[rawElementClassName.length - 1] === ";") {
                elementClassName = rawElementClassName.substring(1, rawElementClassName.length - 1);
                isPrimitive = false;
            } else {
                elementClassName = rawElementClassName;
                isPrimitive = true;
                throw new Error("Primitive arrays not yet supported");
            }
            var elementType = typeFromClassName(elementClassName);
            return {
                type: 'pointer',
                size: 1,
                isCompatible: function (v) {
                    if (typeof v !== 'object' || !v.hasOwnProperty('length')) {
                        return false;
                    }
                    return v.every(function (element) {
                        return elementType.isCompatible(element);
                    });
                },
                fromJni: function (h, env) {
                    var result = [];
                    var length = env.getArrayLength(h);
                    for (var i = 0; i !== length; i++) {
                        var handle = env.getObjectArrayElement(h, i);
                        try {
                            result.push(elementType.fromJni.call(this, handle, env));
                        } finally {
                            env.deleteLocalRef(handle);
                        }
                    }
                    return result;
                },
                toJni: function (elements, env) {
                    var elementClass = factory.use(elementClassName);
                    var result = env.newObjectArray(elements.length, elementClass.$classHandle, NULL);
                    for (var i = 0; i !== elements.length; i++) {
                        var handle = elementType.toJni.call(this, elements[i], env);
                        env.setObjectArrayElement(result, i, handle);
                    }
                    return result;
                }
            };
        };

        initialize.call(this);
    };

    var VM = function VM(api) {
        let handle = null;
        let attachCurrentThread = null;
        let detachCurrentThread = null;
        let getEnv = null;
        let gDvm = null;

        var initialize = function () {
            // pointer to ```JNIInvokeInterface* JavaVM;```
            handle = Memory.readPointer(api.gDvmJni.add(8));

            /*
             * JNI invocation interface. (see jni.h)
             *
             * struct JNIInvokeInterface {
             *   void*       reserved0;
             *   void*       reserved1;
             *   void*       reserved2;
             *   jint        (*DestroyJavaVM)(JavaVM*);
             *   jint        (*AttachCurrentThread)(JavaVM*, JNIEnv**, void*);
             *   jint        (*DetachCurrentThread)(JavaVM*);
             *   jint        (*GetEnv)(JavaVM*, void**, jint);
             *   jint        (*AttachCurrentThreadAsDaemon)(JavaVM*, JNIEnv**, void*);
             * };
             */
            var vtable = Memory.readPointer(handle);
            attachCurrentThread = new NativeFunction(Memory.readPointer(vtable.add(4 * pointerSize)), 'int32', ['pointer', 'pointer', 'pointer']);
            detachCurrentThread = new NativeFunction(Memory.readPointer(vtable.add(5 * pointerSize)), 'int32', ['pointer']);
            getEnv = new NativeFunction(Memory.readPointer(vtable.add(6 * pointerSize)), 'int32', ['pointer', 'pointer', 'int32']);

            //   gDvm = new gDvm(api);


            var ptrgDvm = Memory.readPointer(api.gDvm.add(0));
            var vtable2 = Memory.readPointer(ptrgDvm);
            //attachCurrentThread = new NativeFunction(Memory.readPointer(vtable.add(4 * pointerSize)), 'int32', ['pointer', 'pointer', 'pointer']);
        };
        /*
         const registryBuiltins = {
         "hasOwnProperty": true,
         "toJSON": true,
         "toString": true,
         "valueOf": true
         };

         function Registry() {
         const cachedFields = {};
         let numCachedFields = 0;

         const registry = Proxy.create({
         has(name) {
         if (registryBuiltins[name] !== undefined)
         return true;
         return findField(name) !== null;
         },
         get(target, name) {
         switch (name) {
         case "hasOwnProperty":
         return this.has;
         case "toJSON":
         return toJSON;
         case "toString":
         return toString;
         case "valueOf":
         return valueOf;
         default:
         return getField(name);
         }
         },
         set(target, name, value) {
         throw new Error("Invalid operation");
         },
         enumerate() {
         return this.keys();
         },
         iterate() {
         const props = this.keys();
         let i = 0;
         return {
         next() {
         if (i === props.length)
         throw StopIteration;
         return props[i++];
         }
         };
         },
         keys() {
         let numFields = api.objc_getClassList(NULL, 0);
         if (numFields !== numCachedFields) {
         // It's impossible to unregister classes in ObjC, so if the number of
         // classes hasn't changed, we can assume that the list is up to date.
         const rawClasses = Memory.alloc(numFields * pointerSize);
         numFields = api.objc_getClassList(rawClasses, numFields);
         for (let i = 0; i !== numFields; i++) {
         const handle = Memory.readPointer(rawClasses.add(i * pointerSize));
         const name = Memory.readUtf8String(api.class_getName(handle));
         cachedClasses[name] = handle;
         }
         }
         return Object.keys(cachedFields);
         }
         });

         function getField(name) {
         const fld = findField(name);
         if (fld === null)
         throw new Error("Unable to find field '" + name + "'");
         return fld;
         }

         function findField(name) {
         let handle = cachedFields[name];
         if (handle === undefined)
         handle = api.objc_lookUpClass(Memory.allocUtf8String(name));
         if (handle.isNull())
         return null;
         return new ObjCObject(handle, true);
         }

         function toJSON() {
         return {};
         }

         function toString() {
         return "Registry";
         }

         function valueOf() {
         return "Registry";
         }

         return registry;
         }
         */

        this.perform = function (fn) {
            var env = this.tryGetEnv();
            var alreadyAttached = env !== null;
            if (!alreadyAttached) {
                env = this.attachCurrentThread();
            }

            var pendingException = null;
            try {
                fn();
            } catch (e) {
                pendingException = e;
            }

            if (!alreadyAttached) {
                this.detachCurrentThread();
            }

            if (pendingException !== null) {
                throw pendingException;
            }
        };

        this.attachCurrentThread = function () {
            // hopefully we will get the pointer for JNIEnv
            // jint        (*AttachCurrentThread)(JavaVM*, JNIEnv**, void*);
            checkJniResult("VM::AttachCurrentThread", attachCurrentThread(handle, scratchBuffer, NULL));
            return new Env(Memory.readPointer(scratchBuffer));
        };

        this.detachCurrentThread = function () {
            checkJniResult("VM::DetachCurrentThread", detachCurrentThread(handle));
        };

        this.getEnv = function () {
            checkJniResult("VM::GetEnv", getEnv(handle, scratchBuffer, JNI_VERSION_1_6));
            return new Env(Memory.readPointer(scratchBuffer));
        };

        this.tryGetEnv = function () {
            var result = getEnv(handle, scratchBuffer, JNI_VERSION_1_6);
            if (result !== JNI_OK) {
                return null;
            }
            return new Env(Memory.readPointer(scratchBuffer));
        };

        initialize.call(this);
    };

    function Env(handle) {
        this.handle = handle;
    }

    (function () {
        var CALL_CONSTRUCTOR_METHOD_OFFSET = 28;

        var CALL_OBJECT_METHOD_OFFSET = 34;
        var CALL_BOOLEAN_METHOD_OFFSET = 37;
        var CALL_BYTE_METHOD_OFFSET = 40;
        var CALL_CHAR_METHOD_OFFSET = 43;
        var CALL_SHORT_METHOD_OFFSET = 46;
        var CALL_INT_METHOD_OFFSET = 49;
        var CALL_LONG_METHOD_OFFSET = 52;
        var CALL_FLOAT_METHOD_OFFSET = 55;
        var CALL_DOUBLE_METHOD_OFFSET = 58;
        var CALL_VOID_METHOD_OFFSET = 61;

        var CALL_STATIC_OBJECT_METHOD_OFFSET = 114;
        var CALL_STATIC_BOOLEAN_METHOD_OFFSET = 117;
        var CALL_STATIC_BYTE_METHOD_OFFSET = 120;
        var CALL_STATIC_CHAR_METHOD_OFFSET = 123;
        var CALL_STATIC_SHORT_METHOD_OFFSET = 126;
        var CALL_STATIC_INT_METHOD_OFFSET = 129;
        var CALL_STATIC_LONG_METHOD_OFFSET = 132;
        var CALL_STATIC_FLOAT_METHOD_OFFSET = 135;
        var CALL_STATIC_DOUBLE_METHOD_OFFSET = 138;
        var CALL_STATIC_VOID_METHOD_OFFSET = 141;

        var GET_OBJECT_FIELD_OFFSET = 95;
        var GET_BOOLEAN_FIELD_OFFSET = 96;
        var GET_BYTE_FIELD_OFFSET = 97;
        var GET_CHAR_FIELD_OFFSET = 98;
        var GET_SHORT_FIELD_OFFSET = 99;
        var GET_INT_FIELD_OFFSET = 100;
        var GET_LONG_FIELD_OFFSET = 101;
        var GET_FLOAT_FIELD_OFFSET = 102;
        var GET_DOUBLE_FIELD_OFFSET = 103;

        /*
         * Set<type>Field Routines
         * void Set<type>Field(JNIEnv *env, jobject obj, jfieldID fieldID, NativeType value);
         */
        var SET_OBJECT_FIELD_OFFSET = 104;
        var SET_BOOLEAN_FIELD_OFFSET = 105;
        var SET_BYTE_FIELD_OFFSET = 106;
        var SET_CHAR_FIELD_OFFSET = 107;
        var SET_SHORT_FIELD_OFFSET = 108;
        var SET_INT_FIELD_OFFSET = 109;
        var SET_LONG_FIELD_OFFSET = 110;
        var SET_FLOAT_FIELD_OFFSET = 111;
        var SET_DOUBLE_FIELD_OFFSET = 112;

        var GET_STATIC_OBJECT_FIELD_OFFSET = 145;
        var GET_STATIC_BOOLEAN_FIELD_OFFSET = 146;
        var GET_STATIC_BYTE_FIELD_OFFSET = 147;
        var GET_STATIC_CHAR_FIELD_OFFSET = 148;
        var GET_STATIC_SHORT_FIELD_OFFSET = 149;
        var GET_STATIC_INT_FIELD_OFFSET = 150;
        var GET_STATIC_LONG_FIELD_OFFSET = 151;
        var GET_STATIC_FLOAT_FIELD_OFFSET = 152;
        var GET_STATIC_DOUBLE_FIELD_OFFSET = 153;

        /*
         * SetStatic<type>Field Routines
         * void SetStatic<type>Field(JNIEnv *env, jclass clazz, jfieldID fieldID, NativeType value);
         */
        var SET_STATIC_OBJECT_FIELD_OFFSET = 154;
        var SET_STATIC_BOOLEAN_FIELD_OFFSET = 155;
        var SET_STATIC_BYTE_FIELD_OFFSET = 156;
        var SET_STATIC_CHAR_FIELD_OFFSET = 157;
        var SET_STATIC_SHORT_FIELD_OFFSET = 158;
        var SET_STATIC_INT_FIELD_OFFSET = 159;
        var SET_STATIC_LONG_FIELD_OFFSET = 160;
        var SET_STATIC_FLOAT_FIELD_OFFSET = 161;
        var SET_STATIC_DOUBLE_FIELD_OFFSET = 162;

        var callMethodOffset = {
            'pointer': CALL_OBJECT_METHOD_OFFSET,
            'uint8': CALL_BOOLEAN_METHOD_OFFSET,
            'int8': CALL_BYTE_METHOD_OFFSET,
            'uint16': CALL_CHAR_METHOD_OFFSET,
            'int16': CALL_SHORT_METHOD_OFFSET,
            'int32': CALL_INT_METHOD_OFFSET,
            'int64': CALL_LONG_METHOD_OFFSET,
            'float': CALL_FLOAT_METHOD_OFFSET,
            'double': CALL_DOUBLE_METHOD_OFFSET,
            'void': CALL_VOID_METHOD_OFFSET
        };

        var callStaticMethodOffset = {
            'pointer': CALL_STATIC_OBJECT_METHOD_OFFSET,
            'uint8': CALL_STATIC_BOOLEAN_METHOD_OFFSET,
            'int8': CALL_STATIC_BYTE_METHOD_OFFSET,
            'uint16': CALL_STATIC_CHAR_METHOD_OFFSET,
            'int16': CALL_STATIC_SHORT_METHOD_OFFSET,
            'int32': CALL_STATIC_INT_METHOD_OFFSET,
            'int64': CALL_STATIC_LONG_METHOD_OFFSET,
            'float': CALL_STATIC_FLOAT_METHOD_OFFSET,
            'double': CALL_STATIC_DOUBLE_METHOD_OFFSET,
            'void': CALL_STATIC_VOID_METHOD_OFFSET
        };

        var getFieldOffset = {
            'pointer': GET_OBJECT_FIELD_OFFSET,
            'uint8': GET_BOOLEAN_FIELD_OFFSET,
            'int8': GET_BYTE_FIELD_OFFSET,
            'uint16': GET_CHAR_FIELD_OFFSET,
            'int16': GET_SHORT_FIELD_OFFSET,
            'int32': GET_INT_FIELD_OFFSET,
            'int64': GET_LONG_FIELD_OFFSET,
            'float': GET_FLOAT_FIELD_OFFSET,
            'double': GET_DOUBLE_FIELD_OFFSET
        };

        var setFieldOffset = {
            'pointer': SET_OBJECT_FIELD_OFFSET,
            'uint8': SET_BOOLEAN_FIELD_OFFSET,
            'int8': SET_BYTE_FIELD_OFFSET,
            'uint16': SET_CHAR_FIELD_OFFSET,
            'int16': SET_SHORT_FIELD_OFFSET,
            'int32': SET_INT_FIELD_OFFSET,
            'int64': SET_LONG_FIELD_OFFSET,
            'float': SET_FLOAT_FIELD_OFFSET,
            'double': SET_DOUBLE_FIELD_OFFSET
        };

        var getStaticFieldOffset = {
            'pointer': GET_STATIC_OBJECT_FIELD_OFFSET,
            'uint8': GET_STATIC_BOOLEAN_FIELD_OFFSET,
            'int8': GET_STATIC_BYTE_FIELD_OFFSET,
            'uint16': GET_STATIC_CHAR_FIELD_OFFSET,
            'int16': GET_STATIC_SHORT_FIELD_OFFSET,
            'int32': GET_STATIC_INT_FIELD_OFFSET,
            'int64': GET_STATIC_LONG_FIELD_OFFSET,
            'float': GET_STATIC_FLOAT_FIELD_OFFSET,
            'double': GET_STATIC_DOUBLE_FIELD_OFFSET
        };

        var setStaticFieldOffset = {
            'pointer': SET_STATIC_OBJECT_FIELD_OFFSET,
            'uint8': SET_STATIC_BOOLEAN_FIELD_OFFSET,
            'int8': SET_STATIC_BYTE_FIELD_OFFSET,
            'uint16': SET_STATIC_CHAR_FIELD_OFFSET,
            'int16': SET_STATIC_SHORT_FIELD_OFFSET,
            'int32': SET_STATIC_INT_FIELD_OFFSET,
            'int64': SET_STATIC_LONG_FIELD_OFFSET,
            'float': SET_STATIC_FLOAT_FIELD_OFFSET,
            'double': SET_STATIC_DOUBLE_FIELD_OFFSET
        };

        var cachedVtable = null;
        var globalRefs = [];
        Env.dispose = function (env) {
            globalRefs.forEach(env.deleteGlobalRef, env);
            globalRefs = [];
        };

        function register(globalRef) {
            globalRefs.push(globalRef);
            return globalRef;
        }

        function vtable() {
            if (cachedVtable === null) {
                cachedVtable = Memory.readPointer(this.handle);
            }
            return cachedVtable;
        }

        // Reference: http://docs.oracle.com/javase/7/docs/technotes/guides/jni/spec/functions.html for the offset
        function proxy(offset, retType, argTypes, wrapper) {
            var impl = null;
            return function () {
                if (impl === null) {
                    impl = new NativeFunction(Memory.readPointer(vtable.call(this).add(offset * pointerSize)), retType, argTypes);
                }
                var args = [impl];
                args = args.concat.apply(args, arguments);
                return wrapper.apply(this, args);
            };
        }

        Env.prototype.findClass = proxy(6, 'pointer', ['pointer', 'pointer'], function (impl, name) {
            var result = impl(this.handle, Memory.allocUtf8String(name));
            var throwable = this.exceptionOccurred();
            if (!throwable.isNull()) {
                this.exceptionClear();
                var description = this.method('pointer', [])(this.handle, throwable, this.javaLangObject().toString);
                var descriptionStr = this.stringFromJni(description);
                this.deleteLocalRef(description);
                this.deleteLocalRef(throwable);
                throw new Error(descriptionStr);
            }
            return result;
        });

        Env.prototype.fromReflectedMethod = proxy(7, 'pointer', ['pointer', 'pointer'], function (impl, method) {
            return impl(this.handle, method);
        });

        Env.prototype.fromReflectedField = proxy(8, 'pointer', ['pointer', 'pointer'], function (impl, method) {
            return impl(this.handle, method);
        });

        Env.prototype.getSuperclass = proxy(10, 'pointer', ['pointer', 'pointer'], function (impl, klass) {
            return impl(this.handle, klass);
        });

        Env.prototype.throw = proxy(13, 'int32', ['pointer', 'pointer'], function (impl, obj) {
            return impl(this.handle, obj);
        });

        Env.prototype.exceptionOccurred = proxy(15, 'pointer', ['pointer'], function (impl) {
            return impl(this.handle);
        });

        Env.prototype.exceptionDescribe = proxy(16, 'void', ['pointer'], function (impl) {
            impl(this.handle);
        });

        Env.prototype.exceptionClear = proxy(17, 'void', ['pointer'], function (impl) {
            impl(this.handle);
        });

        Env.prototype.pushLocalFrame = proxy(19, 'int32', ['pointer', 'int32'], function (impl, capacity) {
            return impl(this.handle, capacity);
        });

        Env.prototype.popLocalFrame = proxy(20, 'pointer', ['pointer', 'pointer'], function (impl, result) {
            return impl(this.handle, result);
        });

        Env.prototype.newGlobalRef = proxy(21, 'pointer', ['pointer', 'pointer'], function (impl, obj) {
            return impl(this.handle, obj);
        });

        Env.prototype.deleteGlobalRef = proxy(22, 'void', ['pointer', 'pointer'], function (impl, globalRef) {
            impl(this.handle, globalRef);
        });

        Env.prototype.deleteLocalRef = proxy(23, 'void', ['pointer', 'pointer'], function (impl, localRef) {
            impl(this.handle, localRef);
        });

        Env.prototype.isSameObject = proxy(24, 'uint8', ['pointer', 'pointer', 'pointer'], function (impl, ref1, ref2) {
            return impl(this.handle, ref1, ref2) ? true : false;
        });

        Env.prototype.getObjectClass = proxy(31, 'pointer', ['pointer', 'pointer'], function (impl, obj) {
            return impl(this.handle, obj);
        });

        Env.prototype.isInstanceOf = proxy(32, 'uint8', ['pointer', 'pointer', 'pointer'], function (impl, obj, klass) {
            return impl(this.handle, obj, klass) ? true : false;
        });

        Env.prototype.getMethodId = proxy(33, 'pointer', ['pointer', 'pointer', 'pointer', 'pointer'], function (impl, klass, name, sig) {
            return impl(this.handle, klass, Memory.allocUtf8String(name), Memory.allocUtf8String(sig));
        });

        Env.prototype.getFieldId = proxy(94, 'pointer', ['pointer', 'pointer', 'pointer', 'pointer'], function (impl, klass, name, sig) {
            return impl(this.handle, klass, Memory.allocUtf8String(name), Memory.allocUtf8String(sig));
        });

        /*
         jobject     (*GetObjectField)(JNIEnv*, jobject, jfieldID);
         jboolean    (*GetBooleanField)(JNIEnv*, jobject, jfieldID);
         jbyte       (*GetByteField)(JNIEnv*, jobject, jfieldID);
         jchar       (*GetCharField)(JNIEnv*, jobject, jfieldID);
         jshort      (*GetShortField)(JNIEnv*, jobject, jfieldID);
         jint        (*GetIntField)(JNIEnv*, jobject, jfieldID);
         */

        Env.prototype.getIntField = proxy(100, 'int32', ['pointer', 'pointer', 'pointer'], function (impl, obj, fieldId) {
            return impl(this.handle, obj, fieldId);
        });

        /*
         jlong       (*GetLongField)(JNIEnv*, jobject, jfieldID);
         jfloat      (*GetFloatField)(JNIEnv*, jobject, jfieldID);
         jdouble     (*GetDoubleField)(JNIEnv*, jobject, jfieldID);
         void        (*SetObjectField)(JNIEnv*, jobject, jfieldID, jobject);
         void        (*SetBooleanField)(JNIEnv*, jobject, jfieldID, jboolean);
         void        (*SetByteField)(JNIEnv*, jobject, jfieldID, jbyte);
         void        (*SetCharField)(JNIEnv*, jobject, jfieldID, jchar);
         void        (*SetShortField)(JNIEnv*, jobject, jfieldID, jshort);
         void        (*SetIntField)(JNIEnv*, jobject, jfieldID, jint);
         void        (*SetLongField)(JNIEnv*, jobject, jfieldID, jlong);
         void        (*SetFloatField)(JNIEnv*, jobject, jfieldID, jfloat);
         void        (*SetDoubleField)(JNIEnv*, jobject, jfieldID, jdouble);
         */

        Env.prototype.getStaticMethodId = proxy(113, 'pointer', ['pointer', 'pointer', 'pointer', 'pointer'], function (impl, klass, name, sig) {
            return impl(this.handle, klass, Memory.allocUtf8String(name), Memory.allocUtf8String(sig));
        });

        Env.prototype.getStaticFieldId = proxy(144, 'pointer', ['pointer', 'pointer', 'pointer', 'pointer'], function (impl, klass, name, sig) {
            return impl(this.handle, klass, Memory.allocUtf8String(name), Memory.allocUtf8String(sig));
        });

        Env.prototype.getStaticIntField = proxy(150, 'int32', ['pointer', 'pointer', 'pointer'], function (impl, obj, fieldId) {
            return impl(this.handle, obj, fieldId);
        });

        Env.prototype.newStringUtf = proxy(167, 'pointer', ['pointer', 'pointer'], function (impl, str) {
            var utf = Memory.allocUtf8String(str);
            return impl(this.handle, utf);
        });

        Env.prototype.getStringUtfChars = proxy(169, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, str) {
            return impl(this.handle, str, NULL);
        });

        Env.prototype.releaseStringUtfChars = proxy(170, 'void', ['pointer', 'pointer', 'pointer'], function (impl, str, utf) {
            impl(this.handle, str, utf);
        });

        Env.prototype.getArrayLength = proxy(171, 'int32', ['pointer', 'pointer'], function (impl, array) {
            return impl(this.handle, array);
        });

        // jobjectArray NewObjectArray(JNIEnv *env, jsize length, jclass elementClass, jobject initialElement);
        Env.prototype.newObjectArray = proxy(172, 'pointer', ['pointer', 'int32', 'pointer', 'pointer'], function (impl, length, elementClass, initialElement) {
            return impl(this.handle, length, elementClass, initialElement);
        });

        Env.prototype.getObjectArrayElement = proxy(173, 'pointer', ['pointer', 'pointer', 'int32'], function (impl, array, index) {
            return impl(this.handle, array, index);
        });

        // void SetObjectArrayElement(JNIEnv *env, jobjectArray array, jsize index, jobject value);
        Env.prototype.setObjectArrayElement = proxy(174, 'void', ['pointer', 'pointer', 'int32', 'pointer'], function (impl, array, index, value) {
            impl(this.handle, array, index, value);
        });

        var cachedMethods = {};
        var method = function (offset, retType, argTypes) {
            var key = offset + "|" + retType + "|" + argTypes.join(":");
            var m = cachedMethods[key];
            if (!m) {
                m = new NativeFunction(Memory.readPointer(vtable.call(this).add(offset * pointerSize)), retType, ['pointer', 'pointer', 'pointer', '...'].concat(argTypes));
                cachedMethods[key] = m;
            }
            return m;
        };

        Env.prototype.constructor = function (argTypes) {
            return method(CALL_CONSTRUCTOR_METHOD_OFFSET, 'pointer', argTypes);
        };

        Env.prototype.method = function (retType, argTypes) {
            var offset = callMethodOffset[retType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + retType);
            return method(offset, retType, argTypes);
        };

        Env.prototype.staticMethod = function (retType, argTypes) {
            var offset = callStaticMethodOffset[retType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + retType);
            return method(offset, retType, argTypes);
        };

        Env.prototype.field = function (fieldType) {
            var offset = getFieldOffset[fieldType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + fieldType);
            return method(offset, fieldType, []);
        };

        Env.prototype.staticField = function (fieldType) {
            var offset = getStaticFieldOffset[fieldType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + fieldType);
            return method(offset, fieldType, []);
        };

        Env.prototype.setField = function (fieldType) {
            var offset = setFieldOffset[fieldType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + fieldType);
            return method(offset, 'void', [fieldType]);
        };

        Env.prototype.setStaticField = function (fieldType) {
            var offset = setStaticFieldOffset[fieldType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + fieldType);
            return method(offset, 'void', [fieldType]);
        };

        var javaLangClass = null;
        Env.prototype.javaLangClass = function () {
            if (javaLangClass === null) {
                var handle = this.findClass("java/lang/Class");
                javaLangClass = {
                    handle: register(this.newGlobalRef(handle)),
                    getName: this.getMethodId(handle, "getName", "()Ljava/lang/String;"),
                    getDeclaredConstructors: this.getMethodId(handle, "getDeclaredConstructors", "()[Ljava/lang/reflect/Constructor;"),
                    getDeclaredMethods: this.getMethodId(handle, "getDeclaredMethods", "()[Ljava/lang/reflect/Method;"),
                    getDeclaredFields: this.getMethodId(handle, "getDeclaredFields", "()[Ljava/lang/reflect/Field;")
                };
                this.deleteLocalRef(handle);
            }
            return javaLangClass;
        };

        var javaLangObject = null;
        Env.prototype.javaLangObject = function () {
            if (javaLangObject === null) {
                var handle = this.findClass("java/lang/Object");
                javaLangObject = {
                    toString: this.getMethodId(handle, "toString", "()Ljava/lang/String;"),
                    getClass: this.getMethodId(handle, "getClass", "()Ljava/lang/Class;")
                };
                this.deleteLocalRef(handle);
            }
            return javaLangObject;
        };

        var javaLangReflectConstructor = null;
        Env.prototype.javaLangReflectConstructor = function () {
            if (javaLangReflectConstructor === null) {
                var handle = this.findClass("java/lang/reflect/Constructor");
                javaLangReflectConstructor = {
                    getGenericParameterTypes: this.getMethodId(handle, "getGenericParameterTypes", "()[Ljava/lang/reflect/Type;")
                };
                this.deleteLocalRef(handle);
            }
            return javaLangReflectConstructor;
        };

        var javaLangReflectMethod = null;
        Env.prototype.javaLangReflectMethod = function () {
            if (javaLangReflectMethod === null) {
                var handle = this.findClass("java/lang/reflect/Method");
                javaLangReflectMethod = {
                    getName: this.getMethodId(handle, "getName", "()Ljava/lang/String;"),
                    getGenericParameterTypes: this.getMethodId(handle, "getGenericParameterTypes", "()[Ljava/lang/reflect/Type;"),
                    getGenericReturnType: this.getMethodId(handle, "getGenericReturnType", "()Ljava/lang/reflect/Type;"),
                    getModifiers: this.getMethodId(handle, "getModifiers", "()I"),
                    isVarArgs: this.getMethodId(handle, "isVarArgs", "()Z")
                };
                this.deleteLocalRef(handle);
            }
            return javaLangReflectMethod;
        };

        var javaLangReflectField = null;
        Env.prototype.javaLangReflectField = function () {
            if (javaLangReflectField === null) {
                var handle = this.findClass("java/lang/reflect/Field");
                javaLangReflectField = {
                    getName: this.getMethodId(handle, "getName", "()Ljava/lang/String;"),
                    getType: this.getMethodId(handle, "getType", "()Ljava/lang/Class;"),
                    getGenericType: this.getMethodId(handle, "getGenericType", "()Ljava/lang/reflect/Type;"),
                    getModifiers: this.getMethodId(handle, "getModifiers", "()I"),
                    toString: this.getMethodId(handle, "toString", '()Ljava/lang/String;')
                };
                this.deleteLocalRef(handle);
            }
            return javaLangReflectField;
        };

        var javaLangReflectModifier = null;
        Env.prototype.javaLangReflectModifier = function () {
            if (javaLangReflectModifier === null) {
                var handle = this.findClass("java/lang/reflect/Modifier");
                javaLangReflectModifier = {
                    PUBLIC: this.getStaticIntField(handle, this.getStaticFieldId(handle, "PUBLIC", "I")),
                    PRIVATE: this.getStaticIntField(handle, this.getStaticFieldId(handle, "PRIVATE", "I")),
                    PROTECTED: this.getStaticIntField(handle, this.getStaticFieldId(handle, "PROTECTED", "I")),
                    STATIC: this.getStaticIntField(handle, this.getStaticFieldId(handle, "STATIC", "I")),
                    FINAL: this.getStaticIntField(handle, this.getStaticFieldId(handle, "FINAL", "I")),
                    SYNCHRONIZED: this.getStaticIntField(handle, this.getStaticFieldId(handle, "SYNCHRONIZED", "I")),
                    VOLATILE: this.getStaticIntField(handle, this.getStaticFieldId(handle, "VOLATILE", "I")),
                    TRANSIENT: this.getStaticIntField(handle, this.getStaticFieldId(handle, "TRANSIENT", "I")),
                    NATIVE: this.getStaticIntField(handle, this.getStaticFieldId(handle, "NATIVE", "I")),
                    INTERFACE: this.getStaticIntField(handle, this.getStaticFieldId(handle, "INTERFACE", "I")),
                    ABSTRACT: this.getStaticIntField(handle, this.getStaticFieldId(handle, "ABSTRACT", "I")),
                    STRICT: this.getStaticIntField(handle, this.getStaticFieldId(handle, "STRICT", "I"))
                };
                this.deleteLocalRef(handle);
            }
            return javaLangReflectModifier;
        };

        var javaLangReflectGenericArrayType = null;
        Env.prototype.javaLangReflectGenericArrayType = function () {
            if (javaLangReflectGenericArrayType === null) {
                var handle = this.findClass("java/lang/reflect/GenericArrayType");
                javaLangReflectGenericArrayType = {
                    handle: register(this.newGlobalRef(handle)),
                    getGenericComponentType: this.getMethodId(handle, "getGenericComponentType", "()Ljava/lang/reflect/Type;")
                };
                this.deleteLocalRef(handle);
            }
            return javaLangReflectGenericArrayType;
        };

        var javaLangString = null;
        Env.prototype.javaLangString = function () {
            if (javaLangString === null) {
                var handle = this.findClass("java/lang/String");
                javaLangString = {
                    handle: register(this.newGlobalRef(handle))
                    // getGenericComponentType: this.getMethodId(handle, "getGenericComponentType", "()Ljava/lang/reflect/Type;")
                };
                this.deleteLocalRef(handle);
            }
            return javaLangString;
        };

        Env.prototype.getClassName = function (klass) {
            var name = this.method('pointer', [])(this.handle, klass, this.javaLangClass().getName);
            var result = this.stringFromJni(name);
            this.deleteLocalRef(name);
            return result;
        };

        Env.prototype.getTypeName = function (type) {
            if (this.isInstanceOf(type, this.javaLangClass().handle)) {
                return this.getClassName(type);
                // } else if (this.isInstanceOf(type, this.javaLangReflectGenericArrayType().handle)) {
                //     return "L";
            } else {
                return "java.lang.Object";
            }
        };

        Env.prototype.getArrayTypeName = function (type) {
            if (this.isInstanceOf(type, this.javaLangClass().handle)) {
                return "[L" + this.getClassName(type) + ";";
            } else {
                // TODO: handle primitive types
                return "[Ljava.lang.Object;";
            }
        };

        Env.prototype.stringFromJni = function (str) {
            var utf = this.getStringUtfChars(str);
            var result = Memory.readUtf8String(utf);
            this.releaseStringUtfChars(str, utf);
            return result;
        };
    })();

    var getApi = function () {
        if (_api !== null) {
            return _api;
        }

        var temporaryApi = {};
        var pending = [
            {
                module: "libdvm.so",
                functions: {
                    // Object* dvmDecodeIndirectRef(Thread* self, jobject jobj);
                    "_Z20dvmDecodeIndirectRefP6ThreadP8_jobject": ["dvmDecodeIndirectRef", 'pointer', ['pointer', 'pointer']],
                    // void dvmUseJNIBridge(Method* method, void* func);
                    "_Z15dvmUseJNIBridgeP6MethodPv": ["dvmUseJNIBridge", 'void', ['pointer', 'pointer']],
                    // ClassObject* dvmFindLoadedClass(const char* descriptor);
                    "_Z18dvmFindLoadedClassPKc": ["dvmFindLoadedClass", 'pointer', ['pointer']],
                    // ClassObject* dvmFindClass(const char* descriptor, Object* loader); TODO maybe add also dvmFindClassNoInit
                    "_Z12dvmFindClassPKcP6Object": ["dvmFindClass", 'pointer', ['pointer', 'pointer']],
                    // Method* dvmFindVirtualMethodHierByDescriptor(const ClassObject* clazz, const char* methodName, const char* descriptor)
                    "_Z36dvmFindVirtualMethodHierByDescriptorPK11ClassObjectPKcS3_": ["dvmFindVirtualMethodHierByDescriptor", 'pointer', ['pointer', 'pointer', 'pointer']],

                    // Method* dvmFindDirectMethodByDescriptor(const ClassObject* clazz, const char* methodName, const char* descriptor);
                    "_Z31dvmFindDirectMethodByDescriptorPK11ClassObjectPKcS3_": ["dvmFindDirectMethodByDescriptor", 'pointer', ['pointer', 'pointer', 'pointer']],
                    // TODO dvm_dalvik_system_DexFile for loading dex files
                    //"": ["dvm_dalvik_system_DexFile", '', []]

                    /* Retrieve the system (a/k/a application) class loader.
                     * The caller must call dvmReleaseTrackedAlloc on the result.
                     * Object* dvmGetSystemClassLoader() */
                    "_Z23dvmGetSystemClassLoaderv": ["dvmGetSystemClassLoader", 'pointer', []],

                    /* Get the method currently being executed by examining the interp stack.
                     * const Method* dvmGetCurrentJNIMethod();
                     */
                    "_Z22dvmGetCurrentJNIMethodv": ["dvmGetCurrentJNIMethod", 'pointer', []],

                    /*  void dvmDumpAllClasses(int flags);
                     *  flags:  0 = only class names, 1 = also class details
                     */
                    "_Z17dvmDumpAllClassesi": ["dvmDumpAllClasses", 'void', ['int32']],

                    // void dvmDumpClass(const ClassObject* clazz, int flags);
                    "_Z12dvmDumpClassPK11ClassObjecti": ["dvmDumpClass", 'void', ['pointer', 'int32']],

                    /*
                     * Gets the begining of the allocation for the HeapSource.
                     */
                    "_Z20dvmHeapSourceGetBasev": ["dvmHeapSourceGetBase", 'pointer', []],

                    /*
                     * Returns a high water mark, between base and limit all objects must have been
                     * allocated.
                     */
                    "_Z21dvmHeapSourceGetLimitv": ["dvmHeapSourceGetLimit", 'pointer', []]
                },
                // Reference: http://osxr.org/android/source/dalvik/vm/Globals.h
                variables: {
                    "gDvmJni": function (address) {
                        this.gDvmJni = address;
                    },
                    "gDvm": function (address) {
                        this.gDvm = address;
                    }
                }
            }
        ];
        var remaining = 0;
        pending.forEach(function (api) {
            var pendingFunctions = api.functions;
            var pendingVariables = api.variables;
            remaining += Object.keys(pendingFunctions).length + Object.keys(pendingVariables).length;
            Module.enumerateExports(api.module, {
                onMatch: function (exp) {
                    var name = exp.name;
                    if (exp.type === 'function') {
                        var signature = pendingFunctions[name];
                        if (signature) {
                            if (typeof signature === 'function') {
                                signature.call(temporaryApi, exp.address);
                            } else {
                                temporaryApi[signature[0]] = new NativeFunction(exp.address, signature[1], signature[2]);
                            }
                            delete pendingFunctions[name];
                            remaining--;
                        }
                    } else if (exp.type === 'variable') {
                        var handler = pendingVariables[name];
                        if (handler) {
                            handler.call(temporaryApi, exp.address);
                            delete pendingVariables[name];
                            remaining--;
                        }
                    }
                    if (remaining === 0) {
                        return 'stop';
                    }
                },
                onComplete: function () {
                }
            });
        });
        if (remaining === 0) {
            _api = temporaryApi;
        }

        return _api;
    };

    var checkJniResult = function (name, result) {
        if (result != JNI_OK) {
            throw new Error(name + " failed: " + result);
        }
    };

    var basename = function (className) {
        return className.slice(className.lastIndexOf(".") + 1);
    };
}).call(this);
