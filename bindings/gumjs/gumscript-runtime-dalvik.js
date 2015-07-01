/* jshint esnext: true, evil: true */
(function () {
    "use strict";

    const flavor = typeof Process === 'undefined' ? 'kernel' : 'user';
    if (flavor !== 'user')
        return;

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
    /* no error */
    const JNI_OK = 0;
    /* generic error */
    const JNI_ERR = -1;
    /* thread detached from the VM */
    const JNI_EDETACHED = -2;
    /* JNI version error */
    const JNI_VERSION = -3;

    const JNI_VERSION_1_6 = 0x00010006;

    const JNI_ABORT = 2;

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

    const Runtime = function Runtime() {
        let api = null;
        let vm = null;
        let classFactory = null;
        let pending = [];

        function initialize() {
            api = getApi();
            if (api !== null) {
                vm = new VM(api);
                classFactory = new ClassFactory(api, vm);
            }
        };

        WeakRef.bind(Runtime, function dispose() {
            if (api !== null) {
                vm.perform(function () {
                    const env = vm.getEnv();
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

        Object.defineProperty(this, 'getApplicationContext', {
            enumerable: true,
            get: function () {
                const currentApplication = Dalvik.use("android.app.ActivityThread").currentApplication();
                return currentApplication.getApplicationContext();
            }
        });

        Object.defineProperty(this, 'api', {
            enumerable: true,
            get: function () {
                if (!this.available) {
                    throw new Error("Dalvik runtime not available");
                }
                return api;
            }
        });

        Object.defineProperty(this, 'debug', {
            enumerable: true,
            get: function (start, end) {
                if (!this.available) {
                    throw new Error("Dalvik runtime not available");
                }
                const gDvm = api.gDvm;
                for (let offset = start; offset < end; offset += 1) {
                    let jdwpAllowed = gDvm.add(offset);
                    try {
                        Memory.writeU8(jdwpAllowed, 0x1);
                    } catch (e) {
                        // TODO
                    }
                }
                return true;
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
                    const classes = [];
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
            value: function (callbacks) {
                _enumerateLoadedClasses(callbacks, true);
            }
        });

        this.runOnUiThread = function (fn) {
            if (!this.available) {
                throw new Error("Dalvik runtime not available");
            }

            vm.perform(function () {
                const ActivityThread = classFactory.use("android.app.ActivityThread");
                const Handler = classFactory.use("android.os.Handler");
                const Looper = classFactory.use("android.os.Looper");

                const looper = Looper.getMainLooper();
                const handler = Handler.$new.overload("android.os.Looper").call(Handler, looper);
                const message = handler.obtainMessage();
                Handler.dispatchMessage.implementation = function (msg) {
                    const sameHandler = this.$isSameObject(handler);
                    if (sameHandler) {
                        const app = ActivityThread.currentApplication();
                        if (app !== null) {
                            Handler.dispatchMessage.implementation = null;
                            fn();
                        }
                    } else {
                        this.dispatchMessage(msg);
                    }
                };
                message.sendToTarget();
            });
        };

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
                        const ActivityThread = classFactory.use("android.app.ActivityThread");
                        const Handler = classFactory.use("android.os.Handler");
                        const Looper = classFactory.use("android.os.Looper");

                        const looper = Looper.getMainLooper();
                        const handler = Handler.$new.overload("android.os.Looper").call(Handler, looper);
                        const message = handler.obtainMessage();
                        Handler.dispatchMessage.implementation = function (msg) {
                            const sameHandler = this.$isSameObject(handler);
                            if (sameHandler) {
                                const app = ActivityThread.currentApplication();
                                if (app !== null) {
                                    Handler.dispatchMessage.implementation = null;
                                    const loader = app.getClassLoader();
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

        this.choose = function (className, callbacks) {
            if (classFactory.loader === null) {
                throw new Error("Not allowed outside Dalvik.perform() callback");
            }
            return classFactory.choose(className, callbacks);
        };

        this.cast = function (obj, C) {
            return classFactory.cast(obj, C);
        };

        this.getThreadPtr = function () {
            return classFactory.getThreadPtr();
        };

        // Reference: http://stackoverflow.com/questions/2848575/how-to-detect-ui-thread-on-android
        this.isMainThread = function () {
            if (classFactory.loader === null) {
                throw new Error("Not allowed outside Dalvik.perform() callback");
            }
            const Looper = classFactory.use("android.os.Looper");
            const mainLooper = Looper.getMainLooper();
            const myLooper = Looper.myLooper();
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

    const ClassFactory = function ClassFactory(api, vm) {
        const factory = this;
        let classes = {};
        let patchedClasses = {};
        let loader = null;

        const initialize = function () {
            api = getApi();
        };

        this.dispose = function (env) {
            for (let entryId in patchedClasses) {
                if (patchedClasses.hasOwnProperty(entryId)) {
                    const entry = patchedClasses[entryId];
                    Memory.writePointer(entry.vtablePtr, entry.vtable);
                    Memory.writeS32(entry.vtableCountPtr, entry.vtableCount);

                    for (let methodId in entry.targetMethods) {
                        if (entry.targetMethods.hasOwnProperty(methodId)) {
                            entry.targetMethods[methodId].implementation = null;
                        }
                    }
                }
            }
            patchedClasses = {};

            for (let classId in classes) {
                if (classes.hasOwnProperty(classId)) {
                    const klass = classes[classId];
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
                const env = vm.getEnv();
                if (loader !== null) {
                    const klassObj = loader.loadClass(className);
                    C = ensureClass(klassObj.$handle, className);
                } else {
                    const handle = env.findClass(className.replace(/\./g, "/"));
                    try {
                        C = ensureClass(handle, className);
                    } finally {
                        env.deleteLocalRef(handle);
                    }
                }
            }
            return new C(C.__handle__, null);
        };

        this.choose = function (className, callbacks) {
            const env = vm.getEnv();
            const klass = this.use(className);

            let enumerateInstances = function (className, callbacks) {
                const thread = Memory.readPointer(env.handle.add(JNI_ENV_OFFSET_SELF));
                const classObject = api.dvmDecodeIndirectRef(thread, klass.$classHandle);

                const pattern = classObject.toMatchPattern();
                const heapSourceBase = api.dvmHeapSourceGetBase();
                const heapSourceLimit = api.dvmHeapSourceGetLimit();
                let ranges = Process.enumerateRangesSync('r--').filter(function (range) {
                    return range.base.toInt32() >= heapSourceBase.toInt32() && range.base.toInt32() <= heapSourceLimit.toInt32();
                });

                if (ranges.length === 0) {
                    ranges = [{base: heapSourceBase, size: heapSourceLimit.toInt32() - heapSourceBase.toInt32()}];
                }
                for (let i = 0; i < ranges.length; i++) {
                    const start = ranges[i].base;
                    let size = ranges[i].size;

                    // is the last range bigger than the heapSourceLimit? => if yes resize it
                    if (i === ranges.length - 1) {
                        const lastBaseAddress = start.toInt32();
                        if (lastBaseAddress + size > heapSourceLimit.toInt32()) {
                            size = heapSourceLimit.toInt32() - lastBaseAddress;
                        }
                    }

                    Memory.scan(start, size, pattern, {
                        onMatch: function (address, size) {
                            if (api.dvmIsValidObject(address)) {
                                Dalvik.perform(function () {
                                    const env = vm.getEnv();
                                    const thread = Memory.readPointer(env.handle.add(JNI_ENV_OFFSET_SELF));
                                    const localReference = api.addLocalReference(thread, address);
                                    let instance;
                                    try {
                                        instance = Dalvik.cast(localReference, klass);
                                    } finally {
                                        env.deleteLocalRef(localReference);
                                    }
                                    const stopMaybe = callbacks.onMatch(instance);
                                    if (stopMaybe === 'stop') {
                                        return 'stop';
                                    }
                                });
                            }
                        },
                        onError: function (reason) {
                            console.log('\n========\nError ' + reason + "\n=========\n");
                        },
                        onComplete: function () {
                            callbacks.onComplete();
                        }
                    });
                }
            };

            if (api.addLocalReference === null) {
                const libdvm = Process.getModuleByName('libdvm.so');
                Memory.scan(libdvm.base, libdvm.size, '2D E9 F0 41 05 46 15 4E 0C 46 7E 44 11 B3 43 68',
                    {
                        onMatch: function (address, size) {
                            // Note that on 32-bit ARM this address must have its least significant bit set to 0 for ARM functions, and 1 for Thumb functions. => So set it to 1
                            if (Process.arch === 'arm') {
                                address = address.or(1);
                            }
                            api.addLocalReference = new NativeFunction(address, 'pointer', ['pointer', 'pointer']);
                            enumerateInstances(className, callbacks);
                            return 'stop';
                        },
                        onError: function (reason) {
                        },
                        onComplete: function () {
                        }
                    });
            } else {
                enumerateInstances(className, callbacks);
            }
        };

        this.cast = function (obj, klass) {
            const handle = obj.hasOwnProperty('$handle') ? obj.$handle : obj;
            const C = klass.$classWrapper;
            return new C(C.__handle__, handle);
        };

        this.getThreadPtr = function () {
            const env = vm.getEnv();
            return Memory.readPointer(env.handle.add(JNI_ENV_OFFSET_SELF));
        };

        function ensureClass(classHandle, cachedName) {
            let env = vm.getEnv();

            const name = cachedName !== null ? cachedName : env.getClassName(classHandle);
            let klass = classes[name];
            if (klass) {
                return klass;
            }

            const superHandle = env.getSuperclass(classHandle);
            let superKlass;
            if (!superHandle.isNull()) {
                superKlass = ensureClass(superHandle, null);
                env.deleteLocalRef(superHandle);
            } else {
                superKlass = null;
            }

            eval("klass = function " + basename(name) + "(classHandle, handle) {" +
                "const env = vm.getEnv();" +
                "this.$classWrapper = klass;" +
                "this.$classHandle = env.newGlobalRef(classHandle);" +
                "this.$handle = (handle !== null) ? env.newGlobalRef(handle) : null;" +
                "this.$weakRef = WeakRef.bind(this, makeHandleDestructor(this.$handle, this.$classHandle));" +
                "};");

            classes[name] = klass;

            function isInstance() {
                return Boolean(klass.$handle);
            }

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
                    const env = vm.getEnv();
                    return env.isSameObject(obj.$handle, this.$handle);
                };

                Object.defineProperty(klass.prototype, 'class', {
                    get: function () {
                        const Clazz = factory.use("java.lang.Class");
                        return factory.cast(this.$classHandle, Clazz);
                    }
                });

                function getObjectClassName(klass) {
                    const env = vm.getEnv();
                    let jklass;
                    if (klass.$handle) {
                        jklass = env.getObjectClass(klass.$handle);
                    } else {
                        jklass = klass.$classHandle;
                    }
                    const className = env.getClassName(jklass);
                    if (klass.$handle) {
                        env.deleteLocalRef(jklass);
                    }
                    return className;
                }

                Object.defineProperty(klass.prototype, "$className", {
                    get: function () {
                        return getObjectClassName(this);
                    }
                });

                Object.defineProperty(klass.prototype, "$kind", {
                    get: function () {
                        let kind;
                        if (isInstance()) {
                            kind = 'instance';
                        } else {
                            kind = 'class';
                        }
                        return kind;
                    }
                });

                addMethodsAndFields();
            }

            const dispose = function () {
                WeakRef.unbind(this.$weakRef);
            };

            function makeConstructor(classHandle, env) {
                const Constructor = env.javaLangReflectConstructor();
                const invokeObjectMethodNoArgs = env.method('pointer', []);

                const jsMethods = [];
                const jsRetType = getTypeFromJniSignature('objectType', name, false);
                const constructors = invokeObjectMethodNoArgs(env.handle, classHandle, env.javaLangClass().getDeclaredConstructors);
                const numConstructors = env.getArrayLength(constructors);
                for (let constructorIndex = 0; constructorIndex !== numConstructors; constructorIndex++) {
                    const constructor = env.getObjectArrayElement(constructors, constructorIndex);
                    try {
                        const methodId = env.fromReflectedMethod(constructor);
                        const jsArgTypes = [];

                        const types = invokeObjectMethodNoArgs(env.handle, constructor, Constructor.getGenericParameterTypes);
                        try {
                            const numTypes = env.getArrayLength(types);
                            for (let typeIndex = 0; typeIndex !== numTypes; typeIndex++) {
                                const t = env.getObjectArrayElement(types, typeIndex);
                                try {
                                    const argType = getTypeFromJniSignature(env.getTypeName(t));
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
                        jsMethods.push(makeMethod(basename(name), CONSTRUCTOR_METHOD, methodId, jsRetType, jsArgTypes, env));
                    } finally {
                        env.deleteLocalRef(constructor);
                    }
                }
                env.deleteLocalRef(constructors);

                if (jsMethods.length === 0)
                    throw new Error("no supported overloads");

                return makeMethodDispatcher("<init>", jsMethods);
            }

            function makeField(name, handle, env) {
                const Field = env.javaLangReflectField();
                const Modifier = env.javaLangReflectModifier();
                const invokeObjectMethodNoArgs = env.method('pointer', []);
                const invokeIntMethodNoArgs = env.method('int32', []);
                const invokeUInt8MethodNoArgs = env.method('uint8', []);

                const fieldId = env.fromReflectedField(handle);
                const fieldType = invokeObjectMethodNoArgs(env.handle, handle, Field.getGenericType);
                const modifiers = invokeIntMethodNoArgs(env.handle, handle, Field.getModifiers);

                // TODO there should be the opportunity to see the modifiers
                const jsType = (modifiers & Modifier.STATIC) !== 0 ? STATIC_FIELD : INSTANCE_FIELD;

                let jsFieldType;
                try {
                    jsFieldType = getTypeFromJniSignature(env.getTypeName(fieldType));
                } catch (e) {
                    return null;
                } finally {
                    env.deleteLocalRef(fieldType);
                }

                const field = createField(jsType, fieldId, jsFieldType, env);

                if (field === null)
                    throw new Error("No supported field");

                return field;
            }

            function createField(type, fieldId, fieldType, env) {
                const targetFieldId = fieldId;
                let originalFieldId = null;

                const rawFieldType = fieldType.type;
                let invokeTarget = null;
                if (type === STATIC_FIELD) {
                    invokeTarget = env.staticField(rawFieldType);
                } else if (type === INSTANCE_FIELD) {
                    invokeTarget = env.field(rawFieldType);
                } else {
                    throw new Error("Should not be the case");
                }

                let frameCapacity = 2;
                const callArgs = [
                    "env.handle",
                    type === INSTANCE_FIELD ? "this.$handle" : "this.$classHandle",
                    "targetFieldId"
                ];


                let returnCapture, returnStatements;
                if (rawFieldType === 'void') {
                    throw new Error("Should not be the case");
                }

                if (fieldType.fromJni) {
                    frameCapacity++;
                    returnCapture = "rawResult = ";
                    returnStatements = "try {" +
                            "result = fieldType.fromJni.call(this, rawResult, env);" +
                        "} finally {env.popLocalFrame(NULL);} " +
                        "return result;";
                } else {
                    returnCapture = "result = ";
                    returnStatements = "env.popLocalFrame(NULL);" +
                        "return result;";
                }

                let getter;
                eval("getter = function () {" +
                        "const isInstance = this.$handle !== null;" +
                        "if (type === INSTANCE_FIELD && isInstance === false) { " +
                            "throw new Error(name + ': cannot get instance field without an instance');" +
                        "}" +
                        "const env = vm.getEnv();" +
                        "if (env.pushLocalFrame(" + frameCapacity + ") !== JNI_OK) {" +
                            "env.exceptionClear();" +
                            "throw new Error(\"Out of memory\");" +
                        "}" +
                        "let result, rawResult;" +
                        "try {" +
                            //"synchronizeVtable.call(this, env, type === INSTANCE_FIELD);" +
                            returnCapture + "invokeTarget(" + callArgs.join(", ") + ");" +
                        "} catch (e) {" +
                            "env.popLocalFrame(NULL);" +
                            "throw e;" +
                        "}" +
                        "const throwable = env.exceptionOccurred();" +
                        "if (!throwable.isNull()) {" +
                            "env.exceptionClear();" +
                            "const description = env.method('pointer', [])(env.handle, throwable, env.javaLangObject().toString);" +
                            "const descriptionStr = env.stringFromJni(description);" +
                            "env.popLocalFrame(NULL);" +
                            "throw new Error(descriptionStr);" +
                        "}" +
                        returnStatements +
                        "}");

                /*
                 * setter
                 */
                let setFunction = null;
                if (type === STATIC_FIELD) {
                    setFunction = env.setStaticField(rawFieldType);
                } else if (type === INSTANCE_FIELD) {
                    setFunction = env.setField(rawFieldType);
                } else {
                    throw new Error("Should not be the case");
                }

                let inputStatement = null;
                if (fieldType.toJni) {
                    inputStatement = "const input = fieldType.toJni.call(this, value, env);";
                } else {
                    inputStatement = "const input = value;";
                }

                let setter;
                eval("setter = function (value) {" +
                        "const isInstance = this.$handle !== null;" +
                        "if (type === INSTANCE_FIELD && isInstance === false) { " +
                            "throw new Error(name + ': cannot set an instance field without an instance');" +
                        "}" +
                        "if (!fieldType.isCompatible(value)) {throw new Error(name + ': input is not compatible');}" +
                            "const env = vm.getEnv();" +
                            "try {" +
                                inputStatement +
                                "setFunction(" + callArgs.join(", ") + ", input);" +
                            "} catch (e) {" +
                                "throw e;" +
                            "}" +
                            "const throwable = env.exceptionOccurred();" +
                            "if (!throwable.isNull()) {" +
                                "env.exceptionClear();" +
                                "const description = env.method('pointer', [])(env.handle, throwable, env.javaLangObject().toString);" +
                                "const descriptionStr = env.stringFromJni(description);" +
                                "env.popLocalFrame(NULL);" +
                                "throw new Error(descriptionStr);" +
                            "}" +
                        "}");

                const f = {};
                Object.defineProperty(f, "value", {
                    enumerable: true,
                    get: function () {
                        return getter.call(this.temp);
                    },
                    set: function (value) {
                        setter.call(this.temp, value);
                    }
                });

                Object.defineProperty(f, 'fieldHolder', {
                    //configurable: true,
                    enumerable: true,
                    value: klass
                });

                Object.defineProperty(f, 'fieldInstanceType', {
                    enumerable: true,
                    value: type
                });

                Object.defineProperty(f, 'fieldType', {
                    enumerable: true,
                    value: fieldType
                });

                return f;
            }

            // This is an assign function which can copy accessors.
            function myAssign(target, ...sources) {
                sources.forEach(source => {
                    Object.defineProperties(target, Object.keys(source).reduce((descriptors, key) => {
                        descriptors[key] = Object.getOwnPropertyDescriptor(source, key);
                        return descriptors;
                    }, {}));
                });
                return target;
            }

            function addMethodsAndFields() {
                const invokeObjectMethodNoArgs = env.method('pointer', []);
                const Method_getName = env.javaLangReflectMethod().getName;
                const Field_getName = env.javaLangReflectField().getName;
                const fieldHandles = klass.__fields__;
                const methodHandles = klass.__methods__;
                const jsMethods = {};
                const jsFields = {};

                const methods = invokeObjectMethodNoArgs(env.handle, classHandle, env.javaLangClass().getDeclaredMethods);
                const numMethods = env.getArrayLength(methods);
                for (let methodIndex = 0; methodIndex < numMethods; methodIndex++) {
                    const method = env.getObjectArrayElement(methods, methodIndex);
                    try {
                        const methodName = invokeObjectMethodNoArgs(env.handle, method, Method_getName);
                        try {
                            const methodjsName = env.stringFromJni(methodName);
                            const methodHandle = env.newGlobalRef(method);
                            methodHandles.push(methodHandle);
                            let jsOverloads;
                            if (jsMethods.hasOwnProperty(methodjsName)) {
                                jsOverloads = jsMethods[methodjsName];
                            } else {
                                jsOverloads = [];
                                jsMethods[methodjsName] = jsOverloads;
                            }
                            jsOverloads.push(methodHandle);
                        } finally {
                            env.deleteLocalRef(methodName);
                        }
                    } finally {
                        env.deleteLocalRef(method);
                    }
                }

                const fields = invokeObjectMethodNoArgs(env.handle, classHandle, env.javaLangClass().getDeclaredFields);
                const numFields = env.getArrayLength(fields);
                for (let fieldIndex = 0; fieldIndex < numFields; fieldIndex++) {
                    const field = env.getObjectArrayElement(fields, fieldIndex);
                    try {
                        const fieldName = invokeObjectMethodNoArgs(env.handle, field, Field_getName);
                        try {
                            const fieldjsName = env.stringFromJni(fieldName);
                            const fieldHandle = env.newGlobalRef(field);
                            fieldHandles.push(fieldHandle);
                            jsFields[fieldjsName] = fieldHandle;
                        } finally {
                            env.deleteLocalRef(fieldName);
                        }
                    } finally {
                        env.deleteLocalRef(field);
                    }
                }

                // define access to the fields in the class (klass)
                const values = myAssign({}, jsFields, jsMethods);
                Object.keys(values).forEach(function (name) {
                    let v = null;
                    Object.defineProperty(klass.prototype, name, {
                        get: function () {
                            if (v === null) {
                                vm.perform(function () {
                                    let f = {};
                                    if (jsFields.hasOwnProperty(name)) {
                                        f = makeField(name, jsFields[name], vm.getEnv());
                                    }

                                    let m = {};
                                    if (jsMethods.hasOwnProperty(name)) {
                                        m = makeMethodFromOverloads(name, jsMethods[name], vm.getEnv());
                                    }
                                    v = myAssign(m, f);
                                });
                            }
                            // TODO for the moment it's an ugly bugfix...
                            v.temp = this;

                            return v;
                        }
                    });
                });
            }

            function makeMethodFromOverloads(name, overloads, env) {
                const Method = env.javaLangReflectMethod();
                const Modifier = env.javaLangReflectModifier();
                const invokeObjectMethodNoArgs = env.method('pointer', []);
                const invokeIntMethodNoArgs = env.method('int32', []);
                const invokeUInt8MethodNoArgs = env.method('uint8', []);

                const methods = overloads.map(function (handle) {
                    const methodId = env.fromReflectedMethod(handle);
                    const retType = invokeObjectMethodNoArgs(env.handle, handle, Method.getGenericReturnType);
                    const argTypes = invokeObjectMethodNoArgs(env.handle, handle, Method.getGenericParameterTypes);
                    const modifiers = invokeIntMethodNoArgs(env.handle, handle, Method.getModifiers);
                    const isVarArgs = invokeUInt8MethodNoArgs(env.handle, handle, Method.isVarArgs) ? true : false;

                    const jsType = (modifiers & Modifier.STATIC) !== 0 ? STATIC_METHOD : INSTANCE_METHOD;

                    const jsArgTypes = [];

                    let jsRetType;
                    try {
                        jsRetType = getTypeFromJniSignature(env.getTypeName(retType));
                    } catch (e) {
                        env.deleteLocalRef(argTypes);
                        return null;
                    } finally {
                        env.deleteLocalRef(retType);
                    }

                    try {
                        const numArgTypes = env.getArrayLength(argTypes);
                        for (let argTypeIndex = 0; argTypeIndex !== numArgTypes; argTypeIndex++) {
                            const t = env.getObjectArrayElement(argTypes, argTypeIndex);
                            try {
                                const argClassName = (isVarArgs && argTypeIndex === numArgTypes - 1) ? env.getArrayTypeName(t) : env.getTypeName(t);
                                const argType = getTypeFromJniSignature(argClassName);
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

                    return makeMethod(name, jsType, methodId, jsRetType, jsArgTypes, env);
                }).filter(function (m) {
                    return m !== null;
                });

                if (methods.length === 0)
                    throw new Error("no supported overloads");

                if (name === "valueOf") {
                    const hasDefaultValueOf = methods.some(function implementsDefaultValueOf(m) {
                        return m.type === INSTANCE_METHOD && m.argumentTypes.length === 0;
                    });
                    if (!hasDefaultValueOf) {
                        const defaultValueOf = function defaultValueOf() {
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
                            value: getTypeFromJniSignature('int')
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
            }

            function makeMethodDispatcher(name, methods) {
                const candidates = {};
                methods.forEach(function (m) {
                    const numArgs = m.argumentTypes.length;
                    let group = candidates[numArgs];
                    if (!group) {
                        group = [];
                        candidates[numArgs] = group;
                    }
                    group.push(m);
                });

                const f = function () {
                    const isInstance = this.$handle !== null;
                    if (methods[0].type !== INSTANCE_METHOD && isInstance) {
                        throw new Error(name + ": cannot call static method by way of an instance");
                    } else if (methods[0].type === INSTANCE_METHOD && !isInstance) {
                        if (name === 'toString') {
                            return "<" + this.$classWrapper.__name__ + ">";
                        }
                        throw new Error(name + ": cannot call instance method without an instance");
                    }
                    const group = candidates[arguments.length];
                    if (!group) {
                        throw new Error(name + ": argument count does not match any overload");
                    }
                    for (let i = 0; i !== group.length; i++) {
                        const method = group[i];
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
                        const group = candidates[arguments.length];
                        if (!group) {
                            throw new Error(name + ": argument count does not match any overload");
                        }

                        const signature = Array.prototype.join.call(arguments, ":");
                        for (let i = 0; i !== group.length; i++) {
                            const method = group[i];
                            const s = method.argumentTypes.map(function (t) {
                                return t.className;
                            }).join(":");
                            if (s === signature) {
                                return method;
                            }
                        }
                        throw new Error(name + ": specified argument types do not match any overload");
                    }
                });

                Object.defineProperty(f, 'methodHolder', {
                    enumerable: true,
                    get: methods[0].methodHolder
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
                    const throwAmbiguousError = function () {
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
            }

            function makeMethod(methodName, type, methodId, retType, argTypes, env) {
                let targetMethodId = methodId;
                let originalMethodId = null;

                const rawRetType = retType.type;
                const rawArgTypes = argTypes.map(function (t) {
                    return t.type;
                });
                let invokeTarget;
                if (type == CONSTRUCTOR_METHOD) {
                    invokeTarget = env.constructor(rawArgTypes);
                } else if (type == STATIC_METHOD) {
                    invokeTarget = env.staticMethod(rawRetType, rawArgTypes);
                } else if (type == INSTANCE_METHOD) {
                    invokeTarget = env.method(rawRetType, rawArgTypes);
                }

                let frameCapacity = 2;
                const argVariableNames = argTypes.map(function (t, i) {
                    return "a" + (i + 1);
                });
                const callArgs = [
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
                let returnCapture, returnStatements;
                if (rawRetType === 'void') {
                    returnCapture = "";
                    returnStatements = "env.popLocalFrame(NULL);";
                } else {
                    if (retType.fromJni) {
                        frameCapacity++;
                        returnCapture = "rawResult = ";
                        returnStatements = "try {" +
                                "result = retType.fromJni.call(this, rawResult, env);" +
                            "} finally {" +
                                "env.popLocalFrame(NULL);" +
                            "}" +
                            "return result;";
                    } else {
                        returnCapture = "result = ";
                        returnStatements = "env.popLocalFrame(NULL);" +
                            "return result;";
                    }
                }
                let f;
                eval("f = function " + methodName + "(" + argVariableNames.join(", ") + ") {" +
                        "const env = vm.getEnv();" +
                        "if (env.pushLocalFrame(" + frameCapacity + ") !== JNI_OK) {" +
                            "env.exceptionClear();" +
                            "throw new Error(\"Out of memory\");" +
                        "}" +
                        "let result, rawResult;" +
                        "try {" +
                            "synchronizeVtable.call(this, env, type === INSTANCE_METHOD);" +
                            returnCapture + "invokeTarget(" + callArgs.join(", ") + ");" +
                        "} catch (e) {" +
                            "env.popLocalFrame(NULL);" +
                            "throw e;" +
                        "}" +
                        "const throwable = env.exceptionOccurred();" +
                        "if (!throwable.isNull()) {" +
                            "env.exceptionClear();" +
                            "const description = env.method('pointer', [])(env.handle, throwable, env.javaLangObject().toString);" +
                            "const descriptionStr = env.stringFromJni(description);" +
                            "env.popLocalFrame(NULL);" +
                            "throw new Error(descriptionStr);" +
                        "}" +
                        returnStatements +
                        "}");

                Object.defineProperty(f, 'methodHolder', {
                    enumerable: true,
                    value: klass
                });

                Object.defineProperty(f, 'type', {
                    enumerable: true,
                    value: type
                });

                let implementation = null;
                function synchronizeVtable(env, instance) {
                    if (originalMethodId === null) {
                        return; // nothing to do – implementation hasn't been replaced
                    }

                    const thread = Memory.readPointer(env.handle.add(JNI_ENV_OFFSET_SELF));
                    const objectPtr = api.dvmDecodeIndirectRef(thread, instance ? this.$handle : this.$classHandle);
                    let classObject;
                    if (instance) {
                        classObject = Memory.readPointer(objectPtr.add(OBJECT_OFFSET_CLAZZ));
                    } else {
                        classObject = objectPtr;
                    }
                    let key = classObject.toString(16);
                    let entry = patchedClasses[key];
                    if (!entry) {
                        const vtablePtr = classObject.add(CLASS_OBJECT_OFFSET_VTABLE);
                        const vtableCountPtr = classObject.add(CLASS_OBJECT_OFFSET_VTABLE_COUNT);
                        const vtable = Memory.readPointer(vtablePtr);
                        const vtableCount = Memory.readS32(vtableCountPtr);

                        const vtableSize = vtableCount * pointerSize;
                        const shadowVtable = Memory.alloc(2 * vtableSize);
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
                    let method = entry.targetMethods[key];
                    if (!method) {
                        const methodIndex = entry.shadowVtableCount++;
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

                            let argsSize = argTypes.reduce(function (acc, t) {
                                return acc + t.size;
                            }, 0);
                            if (type === INSTANCE_METHOD) {
                                argsSize++;
                            }

                            /* make method native (with 0x0100)
                             * insSize and registersSize are set to arguments size
                             */
                            const accessFlags = Memory.readU32(methodId.add(METHOD_OFFSET_ACCESS_FLAGS)) | 0x0100;
                            const registersSize = argsSize;

                            const outsSize = 0;
                            const insSize = argsSize;
                            // parse method arguments
                            const jniArgInfo = 0x80000000;

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
                const Surrogate = function () {
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

        function makeHandleDestructor() {
            const handles = Array.prototype.slice.call(arguments).filter(function (h) {
                return h !== null;
            });
            return function () {
                vm.perform(function () {
                    const env = vm.getEnv();
                    handles.forEach(env.deleteGlobalRef, env);
                });
            };
        }

        function implement(method, fn) {
            const env = vm.getEnv();

            if (method.hasOwnProperty('overloads')) {
                if (method.overloads.length > 1) {
                    throw new Error("Method has more than one overload. Please resolve by for example: `method.overload('int')`");
                }
                method = method.overloads[0];
            }

            const C = method.methodHolder;
            const type = method.type;
            const retType = method.returnType;
            const argTypes = method.argumentTypes;
            const methodName = method.name;
            const rawRetType = retType.type;
            const rawArgTypes = argTypes.map(function (t) {
                return t.type;
            });

            let frameCapacity = 2;
            const argVariableNames = argTypes.map(function (t, i) {
                return "a" + (i + 1);
            });
            const callArgs = argTypes.map(function (t, i) {
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
                    returnCapture = "const result = ";
                    returnStatements = "let rawResult;" +
                        "try {" +
                            "if (retType.isCompatible.call(this, result)) {" +
                                "rawResult = retType.toJni.call(this, result, env);" +
                            "} else {" +
                                "throw new Error(\"Implementation for " + methodName + " expected return value compatible with '" + retType.className + "'.\");" +
                            "}";
                    if (retType.type === 'pointer') {
                        returnStatements += "} catch (e) {" +
                                "env.popLocalFrame(NULL);" +
                                "throw e;" +
                            "}" +
                            "return env.popLocalFrame(rawResult);";
                        returnNothing = "return NULL;";
                    } else {
                        returnStatements += "} finally {" +
                            "env.popLocalFrame(NULL);" +
                            "}" +
                            "return rawResult;";
                        returnNothing = "return 0;";
                    }
                } else {
                    returnCapture = "const result = ";
                    returnStatements = "env.popLocalFrame(NULL);" +
                        "return result;";
                    returnNothing = "return 0;";
                }
            }

            let f;
            eval("f = function " + methodName + "(" + ["envHandle", "thisHandle"].concat(argVariableNames).join(", ") + ") {" +
                    "const env = new Env(envHandle);" +
                    "if (env.pushLocalFrame(" + frameCapacity + ") !== JNI_OK) {" +
                        "return;" +
                    "}" +
                    "const self = " + ((type === INSTANCE_METHOD) ? "new C(C.__handle__, thisHandle);" : "new C(thisHandle, null);") +
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

        function getTypeHelper(type, signature, unbox) {
            switch (type) {
                case 'boolean':
                    return {
                        type: 'uint8',
                        size: 1,
                        byteSize: 1,
                        isCompatible: function (v) {
                            return typeof v === 'boolean';
                        },
                        fromJni: function (v) {
                            return v ? true : false;
                        },
                        toJni: function (v) {
                            return v ? 1 : 0;
                        },
                        memoryRead: Memory.readU8,
                        memoryWrite: Memory.writeU8
                    };
                    break;
                case 'byte':
                    return {
                        type: 'int8',
                        size: 1,
                        byteSize: 1,
                        isCompatible: function (v) {
                            return Number.isInteger(v) && v >= -128 && v <= 127;
                        },
                        memoryRead: Memory.readS8,
                        memoryWrite: Memory.writeS8
                    };
                    break;
                case 'char':
                    return {
                        type: 'uint16',
                        size: 1,
                        byteSize: 2,
                        isCompatible: function (v) {
                            if (typeof v === 'string' && v.length === 1) {
                                const charCode = v.charCodeAt(0);
                                return charCode >= 0 && charCode <= 65535;
                            } else {
                                return false;
                            }
                        },
                        fromJni: function (c) {
                            return String.fromCharCode(c);
                        },
                        toJni: function (s) {
                            return s.charCodeAt(0);
                        },
                        memoryRead: Memory.readU16,
                        memoryWrite: Memory.writeU16
                    };
                    break;
                case 'short':
                    return {
                        type: 'int16',
                        size: 1,
                        byteSize: 2,
                        isCompatible: function (v) {
                            return Number.isInteger(v) && v >= -32768 && v <= 32767;
                        },
                        memoryRead: Memory.readS16,
                        memoryWrite: Memory.writeS16
                    };
                    break;
                case 'int':
                    return {
                        type: 'int32',
                        size: 1,
                        byteSize: 4,
                        isCompatible: function (v) {
                            return Number.isInteger(v) && v >= -2147483648 && v <= 2147483647;
                        },
                        memoryRead: Memory.readS32,
                        memoryWrite: Memory.writeS32
                    };
                    break;
                case 'long':
                    return {
                        type: 'int64',
                        size: 2,
                        byteSize: 8,
                        isCompatible: function (v) {
                            // JavaScripts safe integer range is to small for it
                            return Number.isInteger(v); // && v >= -9223372036854775808 && v <= 9223372036854775807;
                        },
                        memoryRead: Memory.readS64,
                        memoryWrite: Memory.writeS64
                    };
                    break;
                case 'float':
                    return {
                        type: 'float',
                        size: 1,
                        byteSize: 4,
                        isCompatible: function (v) {
                            // TODO
                            return typeof v === 'number';
                        },
                        memoryRead: Memory.readFloat,
                        memoryWrite: Memory.writeFloat
                    };
                    break;
                case 'double':
                    return {
                        type: 'double',
                        size: 2,
                        byteSize: 8,
                        isCompatible: function (v) {
                            // TODO
                            return typeof v === 'number';
                        },
                        memoryRead: Memory.readDouble,
                        memoryWrite: Memory.writeDouble
                    };
                    break;
                case 'void':
                    return {
                        type: 'void',
                        size: 0,
                        byteSize: 0,
                        isCompatible: function (v) {
                            return v === undefined;
                        }
                    };
                    break;
                case '[Z':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return isCompatiblePrimitiveArray(v, 'boolean');
                        },
                        fromJni: function (h, env) {
                            return fromJniPrimitiveArray(h, 'boolean', env.getArrayLength.bind(env), env.getBooleanArrayElements.bind(env), env.releaseBooleanArrayElements.bind(env));
                        },
                        toJni: function (arr, env) {
                            return toJniPrimitiveArray(arr, 'boolean', env.newBooleanArray.bind(env), env.setBooleanArrayRegion.bind(env));
                        }
                    };
                    break;
                case '[B':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return isCompatiblePrimitiveArray(v, 'byte');
                        },
                        fromJni: function (h, env) {
                            return fromJniPrimitiveArray(h, 'byte', env.getArrayLength.bind(env), env.getByteArrayElements.bind(env), env.releaseByteArrayElements.bind(env));
                        },
                        toJni: function (arr, env) {
                            return toJniPrimitiveArray(arr, 'byte', env.newByteArray.bind(env), env.setByteArrayRegion.bind(env));
                        }
                    };
                    break;
                case '[C':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return isCompatiblePrimitiveArray(v, 'char');
                        },
                        fromJni: function (h, env) {
                            return fromJniPrimitiveArray(h, 'char', env.getArrayLength.bind(env), env.getCharArrayElements.bind(env), env.releaseCharArrayElements.bind(env));
                        },
                        toJni: function (arr, env) {
                            return toJniPrimitiveArray(arr, 'char', env.newCharArray.bind(env), env.setCharArrayRegion.bind(env));
                        }
                    };
                    break;
                case '[D':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return isCompatiblePrimitiveArray(v, 'double');
                        },
                        fromJni: function (h, env) {
                            return fromJniPrimitiveArray(h, 'double', env.getArrayLength.bind(env), env.getDoubleArrayElements.bind(env), env.releaseDoubleArrayElements.bind(env));
                        },
                        toJni: function (arr, env) {
                            return toJniPrimitiveArray(arr, 'double', env.newDoubleArray.bind(env), env.setDoubleArrayRegion.bind(env));
                        }
                    };
                    break;
                case '[F':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return isCompatiblePrimitiveArray(v, 'float');
                        },
                        fromJni: function (h, env) {
                            return fromJniPrimitiveArray(h, 'float', env.getArrayLength.bind(env), env.getFloatArrayElements.bind(env), env.releaseFloatArrayElements.bind(env));
                        },
                        toJni: function (arr, env) {
                            return toJniPrimitiveArray(arr, 'float', env.newFloatArray.bind(env), env.setFloatArrayRegion.bind(env));
                        }
                    };
                    break;
                case '[I':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return isCompatiblePrimitiveArray(v, 'int');
                        },
                        fromJni: function (h, env) {
                            return fromJniPrimitiveArray(h, 'int', env.getArrayLength.bind(env), env.getIntArrayElements.bind(env), env.releaseIntArrayElements.bind(env));
                        },
                        toJni: function (arr, env) {
                            return toJniPrimitiveArray(arr, 'int', env.newIntArray.bind(env), env.setIntArrayRegion.bind(env));
                        }
                    };
                    break;
                case '[J':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return isCompatiblePrimitiveArray(v, 'long');
                        },
                        fromJni: function (h, env) {
                            return fromJniPrimitiveArray(h, 'long', env.getArrayLength.bind(env), env.getLongArrayElements.bind(env), env.releaseLongArrayElements.bind(env));
                        },
                        toJni: function (arr, env) {
                            return toJniPrimitiveArray(arr, 'long', env.newLongArray.bind(env), env.setLongArrayRegion.bind(env));
                        }
                    };
                    break;
                case '[S':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return isCompatiblePrimitiveArray(v, 'short');
                        },
                        fromJni: function (h, env) {
                            return fromJniPrimitiveArray(h, 'short', env.getArrayLength.bind(env), env.getShortArrayElements.bind(env), env.releaseShortArrayElements.bind(env));
                        },
                        toJni: function (arr, env) {
                            return toJniPrimitiveArray(arr, 'short', env.newShortArray.bind(env), env.setShortArrayRegion.bind(env));
                        }
                    };
                    break;
                case '[Ljava.lang.String;':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            return typeof v === 'object' && v.hasOwnProperty('length') &&
                                Array.prototype.every.call(v, elem => typeof elem === 'string');
                        },
                        fromJni: function (h, env) {
                            return fromJniObjectArray(h, env.getArrayLength.bind(env), env.getObjectArrayElement.bind(env), env.stringFromJni.bind(env), env.deleteLocalRef.bind(env));
                        },
                        toJni: function (strings, env) {
                            return toJniObjectArray(strings, env.newObjectArray.bind(env), env.javaLangString().handle,
                                function (i, result) {
                                    const s = env.newStringUtf(strings[i]);
                                    try {
                                        env.setObjectArrayElement(result, i, s);
                                    } finally {
                                        env.deleteLocalRef(s);
                                    }
                                });
                        }
                    };
                    break;
                case 'objectArray':
                    const elementType = getTypeFromJniSignature(signature);
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
                            const result = [];
                            const length = env.getArrayLength(h);
                            for (let i = 0; i !== length; i++) {
                                const handle = env.getObjectArrayElement(h, i);
                                try {
                                    result.push(elementType.fromJni.call(this, handle, env));
                                } finally {
                                    env.deleteLocalRef(handle);
                                }
                            }
                            return result;
                        },
                        toJni: function (elements, env) {
                            let classHandle;
                            /*if (signature.indexOf("[") === 0) {
                                if (loader !== null) {
                                    const klassObj = loader.loadClass(signature);
                                    classHandle = klassObj.$classHandle;
                                } else {
                                    classHandle = env.findClass(signature.replace(/\./g, "/"));
                                }
                            } else {*/
                                const elementClass = factory.use(signature);
                                classHandle = elementClass.$classHandle;
                          //  }
                            try {
                                return toJniObjectArray(elements, env.newObjectArray.bind(env), classHandle,
                                    function (i, result) {
                                        const handle = elementType.toJni.call(this, elements[i], env);
                                        try {
                                            env.setObjectArrayElement(result, i, handle);
                                        } finally {
                                            // TODO check if handle is local handle
                                            env.deleteLocalRef(handle);
                                        }
                                    });
                            } finally {
                                // TODO check if handle is local handle
                                env.deleteLocalRef(classHandle);
                            }
                        }
                    };
                    break;
                case 'objectType':
                    return {
                        type: 'pointer',
                        size: 1,
                        isCompatible: function (v) {
                            if (v === null) {
                                return true;
                            } else if ((signature === 'java.lang.CharSequence' || signature === 'java.lang.String') && typeof v === 'string') {
                                return true;
                            }

                            return typeof v === 'object' && v.hasOwnProperty('$handle'); // TODO: improve strictness
                        },
                        fromJni: function (h, env) {
                            if (h.isNull()) {
                                return null;
                            } else if (signature === 'java.lang.String' && unbox) {
                                return env.stringFromJni(h);
                            } else if (this.$handle !== null && env.isSameObject(h, this.$handle)) {
                                return this;
                            } else {
                                return factory.cast(h, factory.use(signature));
                            }
                        },
                        toJni: function (o, env) {
                            if (o === null) {
                                return NULL;
                            } else if (typeof o === 'string') {
                                return env.newStringUtf(o);
                            }
                            // TODO create new localHandle so we will not release our globalHandle
                            return o.$handle;
                        }
                    };
                    break;
                default:
                    break;
            }
        }

        /*
         * http://docs.oracle.com/javase/6/docs/technotes/guides/jni/spec/types.html#wp9502
         * http://www.liaohuqiu.net/posts/android-object-size-dalvik/
         */
        function getTypeFromJniSignature(typeName, className, unbox) {
            let type = getTypeHelper(typeName, className, unbox);
            if (!type) {
                // either a multidimensional array or a non primitive array
                if (typeName.indexOf("[") === 0) {
                    type = getTypeHelper('objectArray', typeName.substring(1), unbox);
                } else if (typeName[0] === "L" && typeName[typeName.length - 1] === ";") {
                    typeName = typeName.substring(1, typeName.length - 1);
                    type = getTypeHelper('objectType', typeName, true);
                } else {
                    type = getTypeHelper('objectType', typeName, true);
                }
            }

            const result = {
                className: typeName
            };
            for (let key in type) {
                if (type.hasOwnProperty(key)) {
                    result[key] = type[key];
                }
            }
            return result;
        }

        function fromJniObjectArray(arr, lengthFunc, getObjectArrayElementFunc, convertFromJniFunc, deleteRefFunc) {
            const result = [];
            const length = lengthFunc(arr);
            for (let i = 0; i !== length; i++) {
                const elem = getObjectArrayElementFunc(arr, i);
                try {
                    result.push(convertFromJniFunc(elem));
                } finally {
                    deleteRefFunc(elem);
                }
            }
            return result;
        }

        function toJniObjectArray(arr, newObjectArrayFunc, classHandle, setObjectArrayFunc) {
            const length = arr.length;
            const result = newObjectArrayFunc(length, classHandle, NULL);
            for (let i = 0; i < length; i++) {
                setObjectArrayFunc(i, result);
            }
            return result;
        }

        function fromJniPrimitiveArray(arr, typename, getArrayLengthFunc, getArrayElementsFunc, releaseArrayElementsFunc) {
            const result = [];
            const type = getTypeFromJniSignature(typename);
            const length = getArrayLengthFunc(arr);
            const cArr = getArrayElementsFunc(arr);
            try {
                const offset = type.byteSize;
                for (let i = 0; i < length; i++) {
                    const value = type.memoryRead(cArr.add(i * offset));
                    if (type.fromJni) {
                        result.push(type.fromJni(value));
                    } else {
                        result.push(value);
                    }
                }
            } finally {
                releaseArrayElementsFunc(arr, cArr);
            }

            return result;
        }

        // we should have Memory.calloc and Memory.free
        function toJniPrimitiveArray(arr, typename, newArrayFunc, setArrayFunc) {
            const length = arr.length;
            const type = getTypeFromJniSignature(typename);
            const result = newArrayFunc(length);
            const cArray = Memory.alloc(length * type.byteSize);
            for (let i = 0; i < length; i++) {
                if (type.toJni) {
                    type.memoryWrite(cArray.add(i * type.byteSize), type.toJni(arr[i]));
                } else {
                    type.memoryWrite(cArray.add(i * type.byteSize), arr[i]);
                }
                //env.deleteLocalRef(s);
            }
            setArrayFunc(result, 0, length, cArray);
            return result;
        }

        function isCompatiblePrimitiveArray(v, typename) {
            return typeof v === 'object' && v.hasOwnProperty('length') &&
                Array.prototype.every.call(v, elem => getTypeFromJniSignature(typename).isCompatible(elem));
        }

        initialize.call(this);
    };

    const VM = function VM(api) {
        let handle = null;
        let attachCurrentThread = null;
        let detachCurrentThread = null;
        let getEnv = null;

        function initialize() {
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
            const vtable = Memory.readPointer(handle);
            attachCurrentThread = new NativeFunction(Memory.readPointer(vtable.add(4 * pointerSize)), 'int32', ['pointer', 'pointer', 'pointer']);
            detachCurrentThread = new NativeFunction(Memory.readPointer(vtable.add(5 * pointerSize)), 'int32', ['pointer']);
            getEnv = new NativeFunction(Memory.readPointer(vtable.add(6 * pointerSize)), 'int32', ['pointer', 'pointer', 'int32']);
        };

        this.perform = function (fn) {
            let env = this.tryGetEnv();
            const alreadyAttached = env !== null;
            if (!alreadyAttached) {
                env = this.attachCurrentThread();
            }

            let pendingException = null;
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
            const envBuf = Memory.alloc(pointerSize);
            checkJniResult("VM::AttachCurrentThread", attachCurrentThread(handle, envBuf, NULL));
            return new Env(Memory.readPointer(envBuf));
        };

        this.detachCurrentThread = function () {
            checkJniResult("VM::DetachCurrentThread", detachCurrentThread(handle));
        };

        this.getEnv = function () {
            const envBuf = Memory.alloc(pointerSize);
            checkJniResult("VM::GetEnv", getEnv(handle, envBuf, JNI_VERSION_1_6));
            return new Env(Memory.readPointer(envBuf));
        };

        this.tryGetEnv = function () {
            const envBuf = Memory.alloc(pointerSize);
            const result = getEnv(handle, envBuf, JNI_VERSION_1_6);
            if (result !== JNI_OK) {
                return null;
            }
            return new Env(Memory.readPointer(envBuf));
        };

        initialize.call(this);
    };

    function Env(handle) {
        this.handle = handle;
    }

    (function () {
        const CALL_CONSTRUCTOR_METHOD_OFFSET = 28;

        const CALL_OBJECT_METHOD_OFFSET = 34;
        const CALL_BOOLEAN_METHOD_OFFSET = 37;
        const CALL_BYTE_METHOD_OFFSET = 40;
        const CALL_CHAR_METHOD_OFFSET = 43;
        const CALL_SHORT_METHOD_OFFSET = 46;
        const CALL_INT_METHOD_OFFSET = 49;
        const CALL_LONG_METHOD_OFFSET = 52;
        const CALL_FLOAT_METHOD_OFFSET = 55;
        const CALL_DOUBLE_METHOD_OFFSET = 58;
        const CALL_VOID_METHOD_OFFSET = 61;

        const CALL_STATIC_OBJECT_METHOD_OFFSET = 114;
        const CALL_STATIC_BOOLEAN_METHOD_OFFSET = 117;
        const CALL_STATIC_BYTE_METHOD_OFFSET = 120;
        const CALL_STATIC_CHAR_METHOD_OFFSET = 123;
        const CALL_STATIC_SHORT_METHOD_OFFSET = 126;
        const CALL_STATIC_INT_METHOD_OFFSET = 129;
        const CALL_STATIC_LONG_METHOD_OFFSET = 132;
        const CALL_STATIC_FLOAT_METHOD_OFFSET = 135;
        const CALL_STATIC_DOUBLE_METHOD_OFFSET = 138;
        const CALL_STATIC_VOID_METHOD_OFFSET = 141;

        const GET_OBJECT_FIELD_OFFSET = 95;
        const GET_BOOLEAN_FIELD_OFFSET = 96;
        const GET_BYTE_FIELD_OFFSET = 97;
        const GET_CHAR_FIELD_OFFSET = 98;
        const GET_SHORT_FIELD_OFFSET = 99;
        const GET_INT_FIELD_OFFSET = 100;
        const GET_LONG_FIELD_OFFSET = 101;
        const GET_FLOAT_FIELD_OFFSET = 102;
        const GET_DOUBLE_FIELD_OFFSET = 103;

        /*
         * Set<type>Field Routines
         * void Set<type>Field(JNIEnv *env, jobject obj, jfieldID fieldID, NativeType value);
         */
        const SET_OBJECT_FIELD_OFFSET = 104;
        const SET_BOOLEAN_FIELD_OFFSET = 105;
        const SET_BYTE_FIELD_OFFSET = 106;
        const SET_CHAR_FIELD_OFFSET = 107;
        const SET_SHORT_FIELD_OFFSET = 108;
        const SET_INT_FIELD_OFFSET = 109;
        const SET_LONG_FIELD_OFFSET = 110;
        const SET_FLOAT_FIELD_OFFSET = 111;
        const SET_DOUBLE_FIELD_OFFSET = 112;

        const GET_STATIC_OBJECT_FIELD_OFFSET = 145;
        const GET_STATIC_BOOLEAN_FIELD_OFFSET = 146;
        const GET_STATIC_BYTE_FIELD_OFFSET = 147;
        const GET_STATIC_CHAR_FIELD_OFFSET = 148;
        const GET_STATIC_SHORT_FIELD_OFFSET = 149;
        const GET_STATIC_INT_FIELD_OFFSET = 150;
        const GET_STATIC_LONG_FIELD_OFFSET = 151;
        const GET_STATIC_FLOAT_FIELD_OFFSET = 152;
        const GET_STATIC_DOUBLE_FIELD_OFFSET = 153;

        /*
         * SetStatic<type>Field Routines
         * void SetStatic<type>Field(JNIEnv *env, jclass clazz, jfieldID fieldID, NativeType value);
         */
        const SET_STATIC_OBJECT_FIELD_OFFSET = 154;
        const SET_STATIC_BOOLEAN_FIELD_OFFSET = 155;
        const SET_STATIC_BYTE_FIELD_OFFSET = 156;
        const SET_STATIC_CHAR_FIELD_OFFSET = 157;
        const SET_STATIC_SHORT_FIELD_OFFSET = 158;
        const SET_STATIC_INT_FIELD_OFFSET = 159;
        const SET_STATIC_LONG_FIELD_OFFSET = 160;
        const SET_STATIC_FLOAT_FIELD_OFFSET = 161;
        const SET_STATIC_DOUBLE_FIELD_OFFSET = 162;

        const callMethodOffset = {
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

        const callStaticMethodOffset = {
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

        const getFieldOffset = {
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

        const setFieldOffset = {
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

        const getStaticFieldOffset = {
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

        const setStaticFieldOffset = {
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

        let cachedVtable = null;
        let globalRefs = [];
        Env.dispose = function (env) {
            globalRefs.forEach(env.deleteGlobalRef, env);
            globalRefs = [];
        };

        function register(globalRef) {
            globalRefs.push(globalRef);
            return globalRef;
        }

        function vtable(instance) {
            if (cachedVtable === null) {
                cachedVtable = Memory.readPointer(instance.handle);
            }
            return cachedVtable;
        }

        // Reference: http://docs.oracle.com/javase/7/docs/technotes/guides/jni/spec/functions.html for the offset
        function proxy(offset, retType, argTypes, wrapper) {
            let impl = null;
            return function () {
                if (impl === null) {
                    impl = new NativeFunction(Memory.readPointer(vtable(this).add(offset * pointerSize)), retType, argTypes);
                }
                let args = [impl];
                args = args.concat.apply(args, arguments);
                return wrapper.apply(this, args);
            };
        }

        Env.prototype.findClass = proxy(6, 'pointer', ['pointer', 'pointer'], function (impl, name) {
            const result = impl(this.handle, Memory.allocUtf8String(name));
            const throwable = this.exceptionOccurred();
            if (!throwable.isNull()) {
                try {
                    this.exceptionClear();
                    const description = this.method('pointer', [])(this.handle, throwable, this.javaLangObject().toString);
                    try {
                        const descriptionStr = this.stringFromJni(description);
                        throw new Error(descriptionStr);
                    } finally {
                        this.deleteLocalRef(description);
                    }
                } finally {
                    this.deleteLocalRef(throwable);
                }
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
            const utf = Memory.allocUtf8String(str);
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

        Env.prototype.newBooleanArray = proxy(175, 'pointer', ['pointer', 'int32'], function (impl, length) {
            return impl(this.handle, length);
        });

        Env.prototype.newByteArray = proxy(176, 'pointer', ['pointer', 'int32'], function (impl, length) {
            return impl(this.handle, length);
        });

        Env.prototype.newCharArray = proxy(177, 'pointer', ['pointer', 'int32'], function (impl, length) {
            return impl(this.handle, length);
        });

        Env.prototype.newShortArray = proxy(178, 'pointer', ['pointer', 'int32'], function (impl, length) {
            return impl(this.handle, length);
        });

        Env.prototype.newIntArray = proxy(179, 'pointer', ['pointer', 'int32'], function (impl, length) {
            return impl(this.handle, length);
        });

        Env.prototype.newLongArray = proxy(180, 'pointer', ['pointer', 'int32'], function (impl, length) {
            return impl(this.handle, length);
        });

        Env.prototype.newFloatArray = proxy(181, 'pointer', ['pointer', 'int32'], function (impl, length) {
            return impl(this.handle, length);
        });

        Env.prototype.newDoubleArray = proxy(182, 'pointer', ['pointer', 'int32'], function (impl, length) {
            return impl(this.handle, length);
        });

        Env.prototype.getBooleanArrayElements = proxy(183, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, array, index) {
            return impl(this.handle, array, NULL);
        });

        Env.prototype.getByteArrayElements = proxy(184, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, array, index) {
            return impl(this.handle, array, NULL);
        });

        Env.prototype.getCharArrayElements = proxy(185, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, array, index) {
            return impl(this.handle, array, NULL);
        });

        Env.prototype.getShortArrayElements = proxy(186, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, array, index) {
            return impl(this.handle, array, NULL);
        });

        Env.prototype.getIntArrayElements = proxy(187, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, array) {
            return impl(this.handle, array, NULL);
        });

        Env.prototype.getLongArrayElements = proxy(188, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, array) {
            return impl(this.handle, array, NULL);
        });

        Env.prototype.getFloatArrayElements = proxy(189, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, array) {
            return impl(this.handle, array, NULL);
        });

        Env.prototype.getDoubleArrayElements = proxy(190, 'pointer', ['pointer', 'pointer', 'pointer'], function (impl, array) {
            return impl(this.handle, array, NULL);
        });

        Env.prototype.releaseBooleanArrayElements = proxy(191, 'pointer', ['pointer', 'pointer', 'pointer', 'int32'], function (impl, array, cArray) {
            impl(this.handle, array, cArray, JNI_ABORT);
        });

        Env.prototype.releaseByteArrayElements = proxy(192, 'pointer', ['pointer', 'pointer', 'pointer', 'int32'], function (impl, array, cArray) {
            impl(this.handle, array, cArray, JNI_ABORT);
        });

        Env.prototype.releaseCharArrayElements = proxy(193, 'pointer', ['pointer', 'pointer', 'pointer', 'int32'], function (impl, array, cArray) {
            impl(this.handle, array, cArray, JNI_ABORT);
        });

        Env.prototype.releaseShortArrayElements = proxy(194, 'pointer', ['pointer', 'pointer', 'pointer', 'int32'], function (impl, array, cArray) {
            impl(this.handle, array, cArray, JNI_ABORT);
        });

        Env.prototype.releaseIntArrayElements = proxy(195, 'pointer', ['pointer', 'pointer', 'pointer', 'int32'], function (impl, array, cArray) {
            impl(this.handle, array, cArray, JNI_ABORT);
        });

        Env.prototype.releaseLongArrayElements = proxy(196, 'pointer', ['pointer', 'pointer', 'pointer', 'int32'], function (impl, array, cArray) {
            impl(this.handle, array, cArray, JNI_ABORT);
        });

        Env.prototype.releaseFloatArrayElements = proxy(197, 'pointer', ['pointer', 'pointer', 'pointer', 'int32'], function (impl, array, cArray) {
            impl(this.handle, array, cArray, JNI_ABORT);
        });

        Env.prototype.releaseDoubleArrayElements = proxy(198, 'pointer', ['pointer', 'pointer', 'pointer', 'int32'], function (impl, array, cArray) {
            impl(this.handle, array, cArray, JNI_ABORT);
        });

        Env.prototype.setBooleanArrayRegion = proxy(207, 'void', ['pointer', 'pointer', 'int32', 'int32', 'pointer'], function (impl, array, start, length, cArray) {
            impl(this.handle, array, start, length, cArray);
        });

        Env.prototype.setByteArrayRegion = proxy(208, 'void', ['pointer', 'pointer', 'int32', 'int32', 'pointer'], function (impl, array, start, length, cArray) {
            impl(this.handle, array, start, length, cArray);
        });

        Env.prototype.setCharArrayRegion = proxy(209, 'void', ['pointer', 'pointer', 'int32', 'int32', 'pointer'], function (impl, array, start, length, cArray) {
            impl(this.handle, array, start, length, cArray);
        });

        Env.prototype.setShortArrayRegion = proxy(210, 'void', ['pointer', 'pointer', 'int32', 'int32', 'pointer'], function (impl, array, start, length, cArray) {
            impl(this.handle, array, start, length, cArray);
        });

        Env.prototype.setIntArrayRegion = proxy(211, 'void', ['pointer', 'pointer', 'int32', 'int32', 'pointer'], function (impl, array, start, length, cArray) {
            impl(this.handle, array, start, length, cArray);
        });

        Env.prototype.setLongArrayRegion = proxy(212, 'void', ['pointer', 'pointer', 'int32', 'int32', 'pointer'], function (impl, array, start, length, cArray) {
            impl(this.handle, array, start, length, cArray);
        });

        Env.prototype.setFloatArrayRegion = proxy(213, 'void', ['pointer', 'pointer', 'int32', 'int32', 'pointer'], function (impl, array, start, length, cArray) {
            impl(this.handle, array, start, length, cArray);
        });

        Env.prototype.setDoubleArrayRegion = proxy(214, 'void', ['pointer', 'pointer', 'int32', 'int32', 'pointer'], function (impl, array, start, length, cArray) {
            impl(this.handle, array, start, length, cArray);
        });

        const cachedMethods = {};
        function method(offset, retType, argTypes) {
            const key = offset + "|" + retType + "|" + argTypes.join(":");
            let m = cachedMethods[key];
            if (!m) {
                m = new NativeFunction(Memory.readPointer(vtable(this).add(offset * pointerSize)), retType, ['pointer', 'pointer', 'pointer', '...'].concat(argTypes));
                cachedMethods[key] = m;
            }
            return m;
        }

        Env.prototype.constructor = function (argTypes) {
            return method(CALL_CONSTRUCTOR_METHOD_OFFSET, 'pointer', argTypes);
        };

        Env.prototype.method = function (retType, argTypes) {
            const offset = callMethodOffset[retType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + retType);
            return method(offset, retType, argTypes);
        };

        Env.prototype.staticMethod = function (retType, argTypes) {
            const offset = callStaticMethodOffset[retType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + retType);
            return method(offset, retType, argTypes);
        };

        Env.prototype.field = function (fieldType) {
            const offset = getFieldOffset[fieldType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + fieldType);
            return method(offset, fieldType, []);
        };

        Env.prototype.staticField = function (fieldType) {
            const offset = getStaticFieldOffset[fieldType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + fieldType);
            return method(offset, fieldType, []);
        };

        Env.prototype.setField = function (fieldType) {
            const offset = setFieldOffset[fieldType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + fieldType);
            return method(offset, 'void', [fieldType]);
        };

        Env.prototype.setStaticField = function (fieldType) {
            const offset = setStaticFieldOffset[fieldType];
            if (offset === undefined)
                throw new Error("Unsupported type: " + fieldType);
            return method(offset, 'void', [fieldType]);
        };

        let javaLangClass = null;
        Env.prototype.javaLangClass = function () {
            if (javaLangClass === null) {
                const handle = this.findClass("java/lang/Class");
                try {
                    javaLangClass = {
                        handle: register(this.newGlobalRef(handle)),
                        getName: this.getMethodId(handle, "getName", "()Ljava/lang/String;"),
                        getDeclaredConstructors: this.getMethodId(handle, "getDeclaredConstructors", "()[Ljava/lang/reflect/Constructor;"),
                        getDeclaredMethods: this.getMethodId(handle, "getDeclaredMethods", "()[Ljava/lang/reflect/Method;"),
                        getDeclaredFields: this.getMethodId(handle, "getDeclaredFields", "()[Ljava/lang/reflect/Field;")
                    };
                } finally {
                    this.deleteLocalRef(handle);
                }
            }
            return javaLangClass;
        };

        let javaLangObject = null;
        Env.prototype.javaLangObject = function () {
            if (javaLangObject === null) {
                const handle = this.findClass("java/lang/Object");
                try {
                    javaLangObject = {
                        toString: this.getMethodId(handle, "toString", "()Ljava/lang/String;"),
                        getClass: this.getMethodId(handle, "getClass", "()Ljava/lang/Class;")
                    };
                } finally {
                    this.deleteLocalRef(handle);
                }
            }
            return javaLangObject;
        };

        let javaLangReflectConstructor = null;
        Env.prototype.javaLangReflectConstructor = function () {
            if (javaLangReflectConstructor === null) {
                const handle = this.findClass("java/lang/reflect/Constructor");
                try {
                    javaLangReflectConstructor = {
                        getGenericParameterTypes: this.getMethodId(handle, "getGenericParameterTypes", "()[Ljava/lang/reflect/Type;")
                    };
                } finally {
                    this.deleteLocalRef(handle);
                }
            }
            return javaLangReflectConstructor;
        };

        let javaLangReflectMethod = null;
        Env.prototype.javaLangReflectMethod = function () {
            if (javaLangReflectMethod === null) {
                const handle = this.findClass("java/lang/reflect/Method");
                try {
                    javaLangReflectMethod = {
                        getName: this.getMethodId(handle, "getName", "()Ljava/lang/String;"),
                        getGenericParameterTypes: this.getMethodId(handle, "getGenericParameterTypes", "()[Ljava/lang/reflect/Type;"),
                        getGenericReturnType: this.getMethodId(handle, "getGenericReturnType", "()Ljava/lang/reflect/Type;"),
                        getModifiers: this.getMethodId(handle, "getModifiers", "()I"),
                        isVarArgs: this.getMethodId(handle, "isVarArgs", "()Z")
                    };
                } finally {
                    this.deleteLocalRef(handle);
                }
            }
            return javaLangReflectMethod;
        };

        let javaLangReflectField = null;
        Env.prototype.javaLangReflectField = function () {
            if (javaLangReflectField === null) {
                const handle = this.findClass("java/lang/reflect/Field");
                try {
                    javaLangReflectField = {
                        getName: this.getMethodId(handle, "getName", "()Ljava/lang/String;"),
                        getType: this.getMethodId(handle, "getType", "()Ljava/lang/Class;"),
                        getGenericType: this.getMethodId(handle, "getGenericType", "()Ljava/lang/reflect/Type;"),
                        getModifiers: this.getMethodId(handle, "getModifiers", "()I"),
                        toString: this.getMethodId(handle, "toString", '()Ljava/lang/String;')
                    };
                } finally {
                    this.deleteLocalRef(handle);
                }
            }
            return javaLangReflectField;
        };

        let javaLangReflectModifier = null;
        Env.prototype.javaLangReflectModifier = function () {
            if (javaLangReflectModifier === null) {
                const handle = this.findClass("java/lang/reflect/Modifier");
                try {
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
                } finally {
                    this.deleteLocalRef(handle);
                }
            }
            return javaLangReflectModifier;
        };

        let javaLangReflectGenericArrayType = null;
        Env.prototype.javaLangReflectGenericArrayType = function () {
            if (javaLangReflectGenericArrayType === null) {
                const handle = this.findClass("java/lang/reflect/GenericArrayType");
                try {
                    javaLangReflectGenericArrayType = {
                        handle: register(this.newGlobalRef(handle)),
                        getGenericComponentType: this.getMethodId(handle, "getGenericComponentType", "()Ljava/lang/reflect/Type;")
                    };
                } finally {
                    this.deleteLocalRef(handle);
                }
            }
            return javaLangReflectGenericArrayType;
        };

        let javaLangString = null;
        Env.prototype.javaLangString = function () {
            if (javaLangString === null) {
                const handle = this.findClass("java/lang/String");
                try {
                    javaLangString = {
                        handle: register(this.newGlobalRef(handle))
                    };
                } finally {
                    this.deleteLocalRef(handle);
                }
            }
            return javaLangString;
        };

        Env.prototype.getClassName = function (classHandle) {
            const name = this.method('pointer', [])(this.handle, classHandle, this.javaLangClass().getName);
            try {
                return this.stringFromJni(name);
            } finally {
                this.deleteLocalRef(name);
            }
        };

        // TODO
        Env.prototype.getTypeName = function (type) {
            if (this.isInstanceOf(type, this.javaLangClass().handle)) {
                return this.getClassName(type);
                // } else if (this.isInstanceOf(type, this.javaLangReflectGenericArrayType().handle)) {
                //     return "L";
            } else {
                return "java.lang.Object";
            }
        };

        // TODO
        Env.prototype.getArrayTypeName = function (type) {
            if (this.isInstanceOf(type, this.javaLangClass().handle)) {
                return "[L" + this.getClassName(type) + ";";
            } else {
                // TODO: handle primitive types
                return "[Ljava.lang.Object;";
            }
        };

        Env.prototype.stringFromJni = function (str) {
            const utf = this.getStringUtfChars(str);
            try {
                const result = Memory.readUtf8String(utf);
                return result;
            } finally {
                this.releaseStringUtfChars(str, utf);
            }
        };
    })();

    function getApi() {
        if (_api !== null) {
            return _api;
        }

        const temporaryApi = {
            addLocalReference: null
        };
        const pending = [
            {
                module: "libdvm.so",
                functions: {
                    /*
                     * Converts an indirect reference to to an object reference.
                     */
                    "_Z20dvmDecodeIndirectRefP6ThreadP8_jobject": ["dvmDecodeIndirectRef", 'pointer', ['pointer', 'pointer']],

                    "_Z15dvmUseJNIBridgeP6MethodPv": ["dvmUseJNIBridge", 'void', ['pointer', 'pointer']],
                    // bool dvmAddToReferenceTable(ReferenceTable* pRef, Object* obj)
                    // not needed anymore  "_Z22dvmAddToReferenceTableP14ReferenceTableP6Object": ["dvmAddToReferenceTable", 'uint8', ['pointer', 'pointer']],
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
                     * Returns the base of the HeapSource.
                     */
                    "_Z20dvmHeapSourceGetBasev": ["dvmHeapSourceGetBase", 'pointer', []],

                    /*
                     * Returns the limit of the HeapSource.
                     */
                    "_Z21dvmHeapSourceGetLimitv": ["dvmHeapSourceGetLimit", 'pointer', []],

                    /*
                     *  Returns true if the pointer points to a valid object.
                     */
                    "_Z16dvmIsValidObjectPK6Object": ["dvmIsValidObject", 'uint8', ['pointer']]
                },
                // Reference: http://osxr.org/android/source/dalvik/vm/Globals.h
                variables: {
                    "gDvmJni": function (address) {
                        this.gDvmJni = address;
                    },
                    "gDvm": function (address) {
                        this.gDvm = address;
                    },
                    "dvm_dalvik_system_DexFile": function (address) {
                        this.dvmDalvikSystemDexFile = address;
                    }
                }
            }
        ];
        let remaining = 0;
        pending.forEach(function (api) {
            const pendingFunctions = api.functions;
            const pendingVariables = api.variables;
            remaining += Object.keys(pendingFunctions).length + Object.keys(pendingVariables).length;
            Module.enumerateExports(api.module, {
                onMatch: function (exp) {
                    const name = exp.name;
                    if (exp.type === 'function') {
                        const signature = pendingFunctions[name];
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
                        const handler = pendingVariables[name];
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
    }

    function checkJniResult (name, result) {
        if (result != JNI_OK) {
            throw new Error(name + " failed: " + result);
        }
    }

    function basename(className) {
        return className.slice(className.lastIndexOf(".") + 1);
    };
}).call(this);
