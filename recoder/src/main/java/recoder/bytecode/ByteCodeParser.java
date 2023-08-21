/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import java.io.DataInput;
import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import recoder.ParserException;
import recoder.abstraction.ElementValuePair;
import recoder.abstraction.TypeArgument;
import recoder.abstraction.TypeArgument.WildcardMode;
import recoder.convenience.Naming;

/**
 * Simple ByteCode parser.
 *
 * @author AL
 */
public class ByteCodeParser {

    // Warning: this instance is not reentrant at all

    protected final static byte CLASS = 7;
    protected final static byte FIELD_REF = 9;
    protected final static byte METHOD_REF = 10;
    protected final static byte INTERFACE_METHOD_REF = 11;
    protected final static byte STRING = 8;
    protected final static byte INTEGER = 3;
    protected final static byte FLOAT = 4;
    protected final static byte LONG = 5;
    protected final static byte DOUBLE = 6;
    protected final static byte NAME_AND_TYPE = 12;
    protected final static byte UTF8 = 1;
    // this is not thread-safe, but fast
    private final String[] longRes = new String[256];
    /**
     * TODO this is a very, very ugly hack and might not always work (see readMethodInfo())
     */
    private final Set<String> staticInners = new HashSet<>(256);
    /**
     * wether or not to read java 5 signatures (i.e. generic information etc...)
     */
    public boolean readJava5Signatures = true;
    private DataInput in;
    private String className;
    private String fullName;
    private String pathPrefix;
    private String shortName;
    private String superName;
    private int accessFlags;
    private String[] interfaceNames;
    private ArrayList<FieldInfo> fields;
    private ArrayList<MethodInfo> methods;
    private ArrayList<ConstructorInfo> constructors;
    private String[] innerClasses;
    private String[] pool;
    private Object currentDefaultValue; // used by readAttributesForMethod
    private AnnotationUseInfo[][] currentParamAnnotations; // used by readAttributesForMethod
    private ClassFile cf;

    public ByteCodeParser() {
        super();
    }

    static String decodeType(String in) throws ByteCodeFormatException {
        int dim = 0;
        int i = 0;
        char c = in.charAt(i);
        if (c == '[') {
            dim = i;
            do {
                i += 1;
                c = in.charAt(i);
            } while (c == '[');
            dim = i - dim;
        }
        String type = null;
        switch (c) {
        case 'B':
            type = "byte";
            break;
        case 'C':
            type = "char";
            break;
        case 'D':
            type = "double";
            break;
        case 'F':
            type = "float";
            break;
        case 'I':
            type = "int";
            break;
        case 'J':
            type = "long";
            break;
        case 'S':
            type = "short";
            break;
        case 'Z':
            type = "boolean";
            break;
        case 'V':
            type = "void";
            break;
        case 'L':
            int j = in.indexOf(';', i);
            type = in.substring(i + 1, j).replace('/', '.').replace('$', '.');
            break;
        default:
            throw new ByteCodeFormatException("Illegal type code");
        }
        return Naming.toArrayTypeName(type, dim);
    }

    public ClassFile parseClassFile(InputStream is, String location)
            throws ParserException, IOException {
        return parseClassFile((DataInput) new DataInputStream(is), location);
    }

    public ClassFile parseClassFile(InputStream is) throws ParserException, IOException {
        return parseClassFile((DataInput) new DataInputStream(is), null);
    }

    public ClassFile parseClassFile(DataInput inStr) throws ParserException, IOException {
        return parseClassFile(inStr, null);
    }

    public ClassFile parseClassFile(DataInput inStr, String location)
            throws ParserException, IOException {
        cf = new ClassFile();

        this.in = inStr;
        if (inStr.readInt() != 0xCAFEBABE) {
            throw new ByteCodeFormatException("Bad magic in bytecode file");
        }
        @SuppressWarnings("all")
        int minorVersion = inStr.readUnsignedShort();
        @SuppressWarnings("all")
        int majorVersion = inStr.readUnsignedShort();
        int constantPoolCount = inStr.readUnsignedShort();
        makeConstantPool(constantPoolCount);
        accessFlags = inStr.readUnsignedShort();
        className = pool[inStr.readUnsignedShort()];
        className = className.replace('/', '.');
        fullName = className.replace('$', '.');
        int ldp = fullName.lastIndexOf('.');
        pathPrefix = ldp > 0 ? fullName.substring(0, ldp) : "";
        shortName = fullName.substring(ldp + 1);
        superName = pool[inStr.readUnsignedShort()];
        if (superName != null) {
            superName = superName.replace('/', '.').replace('$', '.');
        }
        int interfacesCount = inStr.readUnsignedShort();
        interfaceNames = new String[interfacesCount];
        for (int i = 0; i < interfacesCount; i += 1) {
            interfaceNames[i] = pool[inStr.readUnsignedShort()];
            interfaceNames[i] = interfaceNames[i].replace('/', '.').replace('$', '.');
        }
        int fieldsCount = inStr.readUnsignedShort();
        fields = new ArrayList<>(fieldsCount);
        for (int i = 0; i < fieldsCount; i += 1) {
            fields.add(readFieldInfo());
        }
        int methodsCount = inStr.readUnsignedShort();
        methods = new ArrayList<>();
        constructors = new ArrayList<>();
        for (int i = 0; i < methodsCount; i += 1) {
            MethodInfo minfo = readMethodInfo();
            if (minfo == null) {
                // class initializer: do nothing
            } else if (minfo instanceof ConstructorInfo) {
                constructors.add((ConstructorInfo) minfo);
            } else {
                methods.add(minfo);
            }
        }
        ArrayList<AnnotationUseInfo> annotations = new ArrayList<>();
        ArrayList<TypeParameterInfo> typeParams = new ArrayList<>();
        ArrayList<List<TypeArgumentInfo>> typeArgList = new ArrayList<>();
        ArrayList<String> typeNames = new ArrayList<>();
        innerClasses = readAttributesForClassFile(annotations, typeParams, typeArgList, typeNames);
        annotations.trimToSize();
        typeParams.trimToSize();
        pool = null;

        cf.setLocation(location);
        cf.setPhysicalName(className);
        cf.setFullName(fullName);
        cf.setName(shortName);
        cf.setSuperName(superName);
        cf.setAccessFlags(accessFlags);
        cf.setInterfaceNames(interfaceNames);
        fields.trimToSize();
        cf.setFields(fields);
        constructors.trimToSize();
        cf.setConstructors(constructors);
        methods.trimToSize();
        cf.setMethods(methods);
        cf.setInnerClassNames(innerClasses);
        cf.setAnnotations(annotations);
        cf.setTypeParameters(typeParams);
        if (typeArgList.size() > 0) {
            cf.superClassTypeArguments = typeArgList.get(0);
            if (typeArgList.size() > 1) {
                @SuppressWarnings("unchecked")
                ArrayList<TypeArgumentInfo>[] arrayLists = new ArrayList[typeArgList.size() - 1];
                cf.superInterfacesTypeArguments = arrayLists;
                for (int i = 1; i < typeArgList.size(); i++) {
                    cf.superInterfacesTypeArguments[i - 1] = typeArgList.get(i);
                }
            }
        }

        return cf;
    }

    protected void makeConstantPool(int count) throws IOException, ByteCodeFormatException {
        pool = new String[count];
        int[] targetIndex = new int[count];
        for (int i = 1; i < count; i += 1) {
            int j;
            byte tag = in.readByte();
            switch (tag) {
            case CLASS:
            case STRING:
                j = in.readUnsignedShort();
                if (pool[j] != null) {
                    pool[i] = pool[j];
                } else {
                    targetIndex[i] = j;
                }
                break;
            case FIELD_REF:
            case METHOD_REF:
            case INTERFACE_METHOD_REF:
            case NAME_AND_TYPE:
                in.skipBytes(4);
                break;
            case INTEGER:
                pool[i] = String.valueOf(in.readInt());
                break;
            case FLOAT:
                pool[i] = String.valueOf(in.readFloat());
                break;
            case LONG:
                pool[i] = String.valueOf(in.readLong());
                i += 1; // strange, but true
                break;
            case DOUBLE:
                pool[i] = String.valueOf(in.readDouble());
                i += 1; // strange, but true
                break;
            case UTF8:
                pool[i] = in.readUTF();
                break;
            default:
                throw new ByteCodeFormatException("Bad Constant Pool Type " + tag);
            }
        }
        // 2nd pass
        for (int i = 1; i < count; i += 1) {
            if (targetIndex[i] > 0) {
                pool[i] = pool[targetIndex[i]];
            }
        }
    }

    private String[] decodeTypes(String inStr) throws ByteCodeFormatException {
        int count = 0;
        if (inStr.charAt(0) != '(') {
            throw new ByteCodeFormatException("Bad method descriptor");
        }
        boolean returnValue = false;
        int i = 1;
        while (i < inStr.length()) {
            int dim = 0;
            char c = inStr.charAt(i);
            if (c == ')') {
                if (returnValue) {
                    throw new ByteCodeFormatException("Bad method descriptor");
                }
                returnValue = true;
                i += 1;
                c = inStr.charAt(i);
            }
            if (c == '[') {
                dim = i;
                do {
                    i += 1;
                    c = inStr.charAt(i);
                } while (c == '[');
                dim = i - dim;
            }
            String type = null;
            switch (c) {
            case 'B':
                type = "byte";
                i += 1;
                break;
            case 'C':
                type = "char";
                i += 1;
                break;
            case 'D':
                type = "double";
                i += 1;
                break;
            case 'F':
                type = "float";
                i += 1;
                break;
            case 'I':
                type = "int";
                i += 1;
                break;
            case 'J':
                type = "long";
                i += 1;
                break;
            case 'S':
                type = "short";
                i += 1;
                break;
            case 'Z':
                type = "boolean";
                i += 1;
                break;
            case 'V':
                if (!returnValue) {
                    throw new ByteCodeFormatException("Void parameter type");
                }
                type = "void";
                i += 1;
                break;
            case 'L':
                int j = inStr.indexOf(';', i);
                type = inStr.substring(i + 1, j).replace('/', '.').replace('$', '.');
                i = j + 1;
                break;
            default:
                throw new ByteCodeFormatException("Illegal type code " + c);
            }
            longRes[count++] = Naming.toArrayTypeName(type, dim);
        }
        String[] r = new String[count];
        System.arraycopy(longRes, 0, r, 0, count);
        return r;
    }

    private String[] readAttributesForMethod(ArrayList<AnnotationUseInfo> emptyListForAnnotations,
            String[] prereadParams, List<TypeArgumentInfo>[] typeArgs,
            List<TypeParameterInfo> typeParams) throws IOException, ByteCodeFormatException {
        String[] exceptions = null;
        int count = in.readUnsignedShort();
        for (int i = 0; i < count; i += 1) {
            String name = pool[in.readUnsignedShort()];
            int length = in.readInt();
            if ("Exceptions".equals(name)) {
                if (exceptions != null) {
                    throw new ByteCodeFormatException("Multiple exceptions lists");
                }
                int number = in.readUnsignedShort();
                exceptions = new String[number];
                for (int j = 0; j < number; j += 1) {
                    exceptions[j] =
                        pool[in.readUnsignedShort()].replace('/', '.').replace('$', '.');
                    // apparently does not use the usual type encoding with
                    // ("L")
                }
            } else if ("Signature".equals(name)) {
                if (readJava5Signatures) {
                    List<TypeArgumentInfo>[] typeArgInfos =
                        readMethodSignature(prereadParams, typeParams);
                    System.arraycopy(typeArgInfos, 0, typeArgs, 0, typeArgs.length);
                } else {
                    in.skipBytes(length);
                }
            } else if ("RuntimeVisibleAnnotation".equals(name)
                    || "RuntimeInvisibleAnnotation".equals(name)) {
                if (readJava5Signatures) {
                    int number = in.readUnsignedShort();
                    emptyListForAnnotations.ensureCapacity(number);
                    for (int j = 0; j < number; j++) {
                        emptyListForAnnotations.add(readAnnotation());
                    }
                } else {
                    in.skipBytes(length);
                }
            } else if ("RuntimeVisibleParameterAnnotations".equals(name)
                    || "RuntimeInvisibleParameterAnnotations".equals(name)) {
                if (readJava5Signatures) {
                    int paramNum = in.readUnsignedByte();
                    currentParamAnnotations = new AnnotationUseInfo[paramNum][];
                    for (int j = 0; j < paramNum; j++) {
                        int number = in.readUnsignedShort();
                        currentParamAnnotations[j] = new AnnotationUseInfo[number];
                        for (int k = 0; k < number; k++) {
                            currentParamAnnotations[j][k] = readAnnotation();
                        }
                    }
                } else {
                    in.skipBytes(length);
                }
            } else if ("AnnotationDefault".equals(name)) {
                if (readJava5Signatures) {
                    if (currentDefaultValue != null) {
                        throw new ByteCodeFormatException("Multiple annotation defaults!");
                    }
                    currentDefaultValue = readElementValue();
                } else {
                    in.skipBytes(length);
                }
            } else {
                in.skipBytes(length);
            }
        }
        return exceptions;
    }

    /**
     * @return the inner classes.
     * @throws IOException
     * @throws ByteCodeFormatException
     */
    private String[] readAttributesForClassFile(
            ArrayList<AnnotationUseInfo> emptyListForAnnotations,
            List<TypeParameterInfo> emptyListForTypeParams,
            List<List<TypeArgumentInfo>> emptyListForTypeArgumentLists,
            List<String> emptyListForTypeNames) throws IOException, ByteCodeFormatException {
        String[] innerClassesRes = null;
        int count = in.readUnsignedShort();
        for (int i = 0; i < count; i++) {
            String name = pool[in.readUnsignedShort()];
            int length = in.readInt();
            if ("InnerClasses".equals(name)) {
                if (innerClassesRes != null) {
                    throw new ByteCodeFormatException("Multiple inner classes lists");
                }
                int number = in.readUnsignedShort();
                innerClassesRes = new String[number];
                int k = 0;
                for (int j = 0; j < number; j++) {
                    String s = readInnerClassInfo();
                    if (s != null) {
                        innerClassesRes[k++] = s;
                    }
                }
                if (k != number) {
                    String[] tmpInnerClassesRes = new String[k];
                    System.arraycopy(innerClassesRes, 0, tmpInnerClassesRes, 0, k);
                    innerClassesRes = tmpInnerClassesRes;
                }
            } else if ("RuntimeVisibleAnnotations".equals(name)
                    || "RuntimeInvisibleAnnotations".equals(name)) {
                if (readJava5Signatures) {
                    if (emptyListForAnnotations.size() != 0) {
                        throw new ByteCodeFormatException("Multiple annotation lists");
                    }
                    int number = in.readUnsignedShort();
                    emptyListForAnnotations.ensureCapacity(number);
                    for (int j = 0; j < number; j++) {
                        emptyListForAnnotations.add(readAnnotation());
                    }
                } else {
                    in.skipBytes(length);
                }
            } else if ("EnclosingMethod".equals(name)) {
                in.skipBytes(length);
            } else if ("Synthetic".equals(name)) {
                in.skipBytes(length);
            } else if ("SourceFile".equals(name)) {
                // not currently used
                in.skipBytes(length);
            } else if ("Signature".equals(name)) {
                if (readJava5Signatures) {
                    ReadClassSignatureResult res = readClassSignature();
                    for (TypeParameterInfo tai : res.typeParams) {
                        emptyListForTypeParams.add(tai);
                    }
                    for (List<TypeArgumentInfo> tai : res.typeArgumentArray) {
                        emptyListForTypeArgumentLists.add(tai);
                    }
                    for (String n : res.typeNameArray) {
                        emptyListForTypeNames.add(n);
                    }
                } else {
                    in.skipBytes(length);
                }
            } else if ("Deprecated".equals(name)) {
                in.skipBytes(length);
            } else {
                in.skipBytes(length);
            }
        }
        return innerClassesRes;
    }

    private String[] readAttributesForField(ArrayList<AnnotationUseInfo> emptyListForAnnotations,
            List<TypeArgumentInfo> emptyListForTypeArgs)
            throws IOException, ByteCodeFormatException {
        assert emptyListForAnnotations != null && emptyListForAnnotations.isEmpty();

        String constant = null;
        String type = null;
        int count = in.readUnsignedShort();
        for (int i = 0; i < count; i += 1) {
            String id = pool[in.readUnsignedShort()];
            int length = in.readInt();
            if ("ConstantValue".equals(id)) {
                if (constant != null) {
                    throw new ByteCodeFormatException("Multiple constant values for field");
                }
                constant = pool[in.readUnsignedShort()];
            } else if ("Signature".equals(id)) {
                if (readJava5Signatures) {
                    type = readFieldSignature(pool[in.readUnsignedShort()], emptyListForTypeArgs);
                } else {
                    in.skipBytes(length);
                }
            } else if ("RuntimeVisibleAnnotation".equals(id)
                    || "RuntimeInvisibleAnnotation".equals(id)) {
                if (readJava5Signatures) {
                    int number = in.readUnsignedShort();
                    emptyListForAnnotations.ensureCapacity(number);
                    for (int j = 0; j < number; j++) {
                        emptyListForAnnotations.add(readAnnotation());
                    }
                } else {
                    in.skipBytes(length);
                }
            } else {
                in.skipBytes(length);
            }
        }
        return new String[] { constant, type };
    }

    FieldInfo readFieldInfo() throws IOException, ByteCodeFormatException {
        int fieldAccessFlags = in.readUnsignedShort();
        String name = pool[in.readUnsignedShort()]; // name
        String type = decodeType(pool[in.readUnsignedShort()]); // descriptor
        ArrayList<AnnotationUseInfo> annotations = new ArrayList<>();
        ArrayList<TypeArgumentInfo> typeArgs = new ArrayList<>();
        String[] tmp = readAttributesForField(annotations, typeArgs); // constant value, typeargs,
                                                                      // annotations, possibly
                                                                      // different type
        String constant = tmp[0];
        if (tmp[1] != null) {
            type = tmp[1];
        }
        FieldInfo res = new FieldInfo(fieldAccessFlags, name, type, cf, constant, typeArgs);
        res.setAnnotations(annotations);
        return res;
    }

    MethodInfo readMethodInfo() throws IOException, ByteCodeFormatException {
        int methAccessFlags = in.readUnsignedShort();
        String name = pool[in.readUnsignedShort()];
        boolean isConstructor = "<init>".equals(name);
        boolean isInitializer = false;
        if (isConstructor) {
            name = shortName;
        } else {
            isInitializer = "<clinit>".equals(name);
        }
        String[] types = decodeTypes(pool[in.readUnsignedShort()]); // descriptor
        ArrayList<AnnotationUseInfo> annotations = new ArrayList<>();
        currentDefaultValue = null;
        currentParamAnnotations = null;
        @SuppressWarnings("unchecked")
        List<TypeArgumentInfo>[] typeArgs = new List[types.length];
        ArrayList<TypeParameterInfo> typeParams = new ArrayList<>();
        String[] exceptions = readAttributesForMethod(annotations, types, typeArgs, typeParams);
        String rtype = types[types.length - 1];
        int firstParam = 0;
        int paramCount = types.length - 1;

        // this.accsesFlags will never (at least with Java 1.5 VM) be STATIC. We have to get the
        // information
        // from the the InnerClasses attribute of the outer class. But how ???
        // if (isConstructor && (this.accessFlags & AccessFlags.STATIC) == 0 &&
        // types[0].equals(pathPrefix)) {
        // TODO this is a very, very ugly hack for now and might not always work. Also see
        // readInnerClassInfo()
        if (isConstructor && types[0].equals(pathPrefix) && !staticInners.contains(fullName)) {
            // we are the constructor of a non-static member class!

            // TODO maybe complain if parent type hasn't been read yet? That should be handled by
            // name info, though
            firstParam = 1;
            paramCount -= 1;
        }
        String[] ptypes = new String[paramCount];
        System.arraycopy(types, firstParam, ptypes, 0, paramCount);
        if (isInitializer) {
            return null;
        }
        MethodInfo res;
        if (isConstructor) {
            res = new ConstructorInfo(methAccessFlags, name, ptypes, exceptions, cf);
        } else {
            if ((accessFlags & 0x2000) != 0) {
                res = new AnnotationPropertyInfo(methAccessFlags, rtype, name, cf,
                    currentDefaultValue);
            } else {
                res = new MethodInfo(methAccessFlags, rtype, name, ptypes, exceptions, cf);
            }
        }
        res.setAnnotations(annotations);
        res.paramAnnotations = currentParamAnnotations;
        if (typeArgs.length != 0) {
            setTypeArgParentRec(typeArgs, res); // and another ugly hack
            res.paramTypeArgs = typeArgs;
        }
        if (typeParams.size() != 0) {
            typeParams.trimToSize();
            res.typeParms = typeParams;
        }
        return res;
    }

    private void setTypeArgParentRec(List<? extends TypeArgument>[] typeArgs, MethodInfo res) {
        for (List<? extends TypeArgument> typeArg : typeArgs) {
            if (typeArg != null) {
                setTypeArgParentRec(typeArg, res);
            }
        }
    }

    private void setTypeArgParentRec(List<? extends TypeArgument> typeArgs, MethodInfo res) {
        for (TypeArgument ta : typeArgs) {
            TypeArgumentInfo tai = (TypeArgumentInfo) ta;
            tai.parent = res;
            if (tai.typeArgs != null) {
                setTypeArgParentRec(tai.typeArgs, res);
            }
        }
    }

    public String readInnerClassInfo() throws IOException {
        String name = pool[in.readUnsignedShort()]; // inner class info index
        if (name != null) {
            name = name.replace('/', '.').replace('$', '.');
        }

        // the next two entries seem to be pretty useless for our purposes
        /* int outerClassInfoIndex = */
        in.readUnsignedShort();
        /* int innerNameIndex = */
        in.readUnsignedShort();
        int innerClassAccessFlags = in.readUnsignedShort();
        if (name != null && (innerClassAccessFlags & AccessFlags.STATIC) != 0) {
            staticInners.add(name);
        }
        if (name != null) {
            // we may still reject this: it might not be a member type!
            if (!fullName.equals(name.substring(0, name.lastIndexOf('.')))) {
                name = null; // this indicates that that type is used, but not that that type is
            }
            // declared here!
            else if (!Character.isJavaIdentifierStart(name.charAt(name.lastIndexOf('.') + 1))) {
                name = null; // anonymous class
            }
        }
        return name;
        // return new InnerClassInfo(accessFlags, name, cf);
    }


    private Object readElementValue() throws IOException, ByteCodeFormatException {
        Object res;
        int tag = in.readByte();
        switch (tag) {
        case 'B':
            res = Byte.valueOf(pool[in.readUnsignedShort()]);
            break;
        case 'C':
            // TODO this needs to be verified !!!!
            res = pool[in.readUnsignedShort()].toCharArray()[0];
            break;
        case 'D':
            res = Double.valueOf(pool[in.readUnsignedShort()]);
            break;
        case 'F':
            res = Float.valueOf(pool[in.readUnsignedShort()]);
            break;
        case 'I':
            res = Integer.valueOf(pool[in.readUnsignedShort()]);
            break;
        case 'J':
            res = Long.valueOf(pool[in.readUnsignedShort()]);
            break;
        case 'S':
            res = Short.valueOf(pool[in.readUnsignedShort()]);
            break;
        case 'Z':
            res = Boolean.valueOf(pool[in.readUnsignedShort()]);
            break;
        case 's':
            res = pool[in.readUnsignedShort()];
            break;
        case 'e':
            String typename = pool[in.readUnsignedShort()];
            String constname = pool[in.readUnsignedShort()];
            res = new EnumConstantReferenceInfo(typename, constname);
            break;
        case 'c':
            String tr = pool[in.readUnsignedShort()];
            tr = tr.replace('/', '.').replace('$', '.');
            res = new TypeNameReferenceInfo(tr);
            break;
        case '@':
            res = readAnnotation();
            break;
        case '[':
            int num = in.readUnsignedShort();
            res = new Object[num];
            for (int i = 0; i < num; i++) {
                ((Object[]) res)[i] = readElementValue();
            }
            break;
        default:
            throw new ByteCodeFormatException("Illegal tag in element-value: " + tag);
        }
        return res;
    }

    private AnnotationUseInfo readAnnotation() throws IOException, ByteCodeFormatException {
        String name = pool[in.readUnsignedShort()]; // annotation index
        if (name == null) {
            throw new ByteCodeFormatException();
        }
        name = name.replace('/', '.').replace('$', '.').substring(1, name.length() - 1);
        int number = in.readUnsignedShort();
        List<ElementValuePair> evpl = new ArrayList<>(number);
        for (int i = 0; i < number; i++) {
            String elementName = pool[in.readUnsignedShort()];
            Object value = readElementValue();
            ElementValuePairInfo evpi = new ElementValuePairInfo(elementName, value, name);
            evpl.add(evpi);
        }
        return new AnnotationUseInfo(name, evpl);
    }

    private ReadClassSignatureResult readClassSignature()
            throws IOException, ByteCodeFormatException {
        ReadClassSignatureResult res = new ReadClassSignatureResult();
        String sig = pool[in.readUnsignedShort()];
        int start = 0;
        if (sig.charAt(0) == '<') { // formal type parameters are present, process.
            res.typeParams = readFormalTypeParameters(sig);
            start = 1;
            for (int o = 1; o > 0; start++) {
                if (sig.charAt(start) == '<') {
                    o++;
                } else if (sig.charAt(start) == '>') {
                    o--;
                }
            }
        }
        List<List<TypeArgumentInfo>> l1 = new ArrayList<>();
        List<String> l2 = new ArrayList<>();
        while (start != sig.length()) {
            // read proper super types
            int end = start;
            int o = 0;
            while (sig.charAt(++end) != ';' || o > 0) {
                if (sig.charAt(end) == '<') {
                    o++;
                } else if (sig.charAt(end) == '>') {
                    o--;
                }
            }
            end++;
            String sig2 = sig.substring(start, end);
            ArrayList<TypeArgumentInfo> ral = new ArrayList<>();
            l2.add(readFieldSignature(sig2, ral));
            l1.add(ral);
            start = end;
        }
        if (res.typeParams == null) {
            res.typeParams = new ArrayList<>();
        }
        res.typeArgumentArray = l1;
        res.typeNameArray = l2;
        return res;
    }

    private List<TypeParameterInfo> readFormalTypeParameters(String sig)
            throws ByteCodeFormatException {
        List<TypeParameterInfo> res = new ArrayList<>();
        int rpos = 1;
        int lpos;
        int cnt = 0;
        // loop until done
        while (sig.charAt(rpos) != '>') { // read until formal type paramters are all read
            cnt++;
            lpos = rpos;
            // read name of type parameter
            while (sig.charAt(rpos) != ':') {
                rpos++;
            }
            String paramName = sig.substring(lpos, rpos); // parameter name
            List<String> boundNames = new ArrayList<>();
            List<List<TypeArgumentInfo>> boundArgs = new ArrayList<>();
            do {
                rpos++; // consume ':'
                lpos = rpos; // first character
                if (sig.charAt(lpos) == '[') {
                    // this may not happen: arrays not allowed as type bounds!
                    throw new ByteCodeFormatException();
                }
                String typeName;
                switch (sig.charAt(lpos)) {
                case ':':
                    typeName = "java.lang.Object"; // allowed for class bound only, but
                    // we assume that bytecode isn't corrupted.
                    break;
                case 'L':
                    while (sig.charAt(rpos) != ';') {
                        rpos++;
                    }
                    typeName = sig.substring(lpos + 1, rpos).replace('/', '.');
                    rpos++; // skip ';'
                    break;
                case 'T':
                    throw new UnsupportedOperationException("TODO");
                default:
                    throw new ByteCodeFormatException();
                }
                int idx = typeName.indexOf('<');
                List<TypeArgumentInfo> typeArgs = null;
                if (idx != -1) {
                    typeArgs = makeTypeArgs(typeName.substring(idx));
                    typeName = typeName.substring(0, idx);
                    rpos += 2; // skip tailing >;
                }
                boundNames.add(typeName);
                boundArgs.add(typeArgs);
            } while (sig.charAt(rpos) == ':'); // continue while there is another bound
            String[] bn = new String[boundNames.size()];
            boundNames.toArray(bn);
            @SuppressWarnings("unchecked")
            List<TypeArgumentInfo>[] tai = new List[boundArgs.size()];
            boundArgs.toArray(tai);
            TypeParameterInfo n = new TypeParameterInfo(paramName, bn, tai, cf);
            res.add(n);
        }
        return res;
    }

    private List<TypeArgumentInfo> makeTypeArgs(String tn) throws ByteCodeFormatException {
        ArrayList<TypeArgumentInfo> res = new ArrayList<>();
        assert tn.charAt(0) == '<';
        int pos = 1; // skip first character
        do {
            WildcardMode wm;
            String typeName = null;
            switch (tn.charAt(pos)) {
            case '+':
                wm = WildcardMode.Extends; // TODO check !!
                pos++;
                break;
            case '-':
                wm = WildcardMode.Super; // TODO check!!
                pos++;
                break;
            case '*':
                wm = WildcardMode.Any;
                pos++;
                break;
            default:
                wm = WildcardMode.None;
                break;
            }
            if (wm != WildcardMode.Any) {
                boolean isTypeVariable = false;
                int dim = 0;
                while (tn.charAt(pos) == '[') {
                    dim++;
                    pos++;
                }
                int rpos = pos;
                switch (tn.charAt(pos)) {
                case 'L':
                    int o = 1;
                    while (rpos < tn.length() && o > 0 && !(tn.charAt(rpos) == ';' && o == 1)) {
                        if (tn.charAt(rpos) == '<') {
                            o++;
                        }
                        if (tn.charAt(rpos) == '>') {
                            o--;
                        }
                        rpos++;
                    }
                    typeName = tn.substring(pos + 1, rpos).replace('/', '.');
                    if (typeName.equals("")) {
                        typeName = "java.lang.Object"; // allowed for class bound only, but
                    }
                    // we assume that bytecode isn't corrupted.
                    while (typeName.endsWith(";") || typeName.endsWith(">")) {
                        typeName = typeName.substring(0, typeName.length() - 1);
                    }
                    typeName = Naming.toArrayTypeName(typeName, dim);
                    rpos++; // skip ';'
                    break;
                case 'T':
                    while (rpos < tn.length() && Character.isJavaIdentifierPart(tn.charAt(rpos))) {
                        rpos++;
                    }
                    typeName = tn.substring(pos + 1, rpos);
                    typeName = Naming.toArrayTypeName(typeName, dim);
                    isTypeVariable = true;
                    rpos++;
                    break;
                case 'B':
                    if (dim == 0) {
                        throw new ByteCodeFormatException(
                            "primitive type not allowed as type argument");
                    }
                    typeName = "byte";
                    rpos++;
                    break;
                case 'C':
                    if (dim == 0) {
                        throw new ByteCodeFormatException(
                            "primitive type not allowed as type argument");
                    }
                    typeName = "char";
                    rpos++;
                    break;
                case 'D':
                    if (dim == 0) {
                        throw new ByteCodeFormatException(
                            "primitive type not allowed as type argument");
                    }
                    typeName = "double";
                    rpos++;
                    break;
                case 'F':
                    if (dim == 0) {
                        throw new ByteCodeFormatException(
                            "primitive type not allowed as type argument");
                    }
                    typeName = "float";
                    rpos++;
                    break;
                case 'I':
                    if (dim == 0) {
                        throw new ByteCodeFormatException(
                            "primitive type not allowed as type argument");
                    }
                    typeName = "int";
                    rpos++;
                    break;
                case 'J':
                    if (dim == 0) {
                        throw new ByteCodeFormatException(
                            "primitive type not allowed as type argument");
                    }
                    typeName = "long";
                    rpos++;
                    break;
                case 'S':
                    if (dim == 0) {
                        throw new ByteCodeFormatException(
                            "primitive type not allowed as type argument");
                    }
                    typeName = "short";
                    rpos++;
                    break;
                case 'Z':
                    if (dim == 0) {
                        throw new ByteCodeFormatException(
                            "primitive type not allowed as type argument");
                    }
                    typeName = "boolean";
                    rpos++;
                    break;
                default:
                    throw new ByteCodeFormatException();
                }
                int idx = typeName.indexOf('<');
                List<TypeArgumentInfo> typeArgs = null;
                if (idx != -1) {
                    typeArgs = makeTypeArgs(typeName.substring(idx));
                    typeName = typeName.substring(0, idx);
                    typeName = Naming.toArrayTypeName(typeName, dim); // TODO double work...
                }
                res.add(new TypeArgumentInfo(wm, typeName.replace('$', '.'), typeArgs, cf,
                    isTypeVariable));
                pos = rpos;
            } else {
                res.add(new TypeArgumentInfo(wm, null, null, cf, false));
            }
        } while (pos < tn.length());
        res.trimToSize();
        return res;
    }

    private String readFieldSignature(String sig, List<TypeArgumentInfo> emptyListForTypeArgs)
            throws IOException, ByteCodeFormatException {
        String res = null;

        int rpos = sig.indexOf('(') + 1;

        int dim = 0;
        while (sig.charAt(rpos) == '[') {
            dim++;
            rpos++;
        }
        switch (sig.charAt(rpos)) {
        case 'L':
            int lpos = rpos;
            while (sig.charAt(rpos) != ';') {
                if (sig.charAt(rpos) == '<') {
                    int talpos = rpos;
                    int o = 1;
                    while (o > 0) {
                        rpos++;
                        if (sig.charAt(rpos) == '<') {
                            o++;
                        }
                        if (sig.charAt(rpos) == '>') {
                            o--;
                        }
                    }
                    String targs = sig.substring(talpos, rpos);
                    emptyListForTypeArgs.addAll(makeTypeArgs(targs));
                }
                rpos++;
            }
            // String typeName = sig.substring(lpos+1,rpos).replace('/','.');
            int idx = sig.indexOf('<');
            res = Naming.toArrayTypeName(
                sig.substring(lpos + 1, idx == -1 ? sig.length() - 1 : idx).replace('/', '.'), dim);
            rpos++; // skip ';'
            break;
        case 'T':
            lpos = rpos;
            while (sig.charAt(rpos) != ';') {
                rpos++;
            }
            res = Naming.toArrayTypeName(sig.substring(lpos + 1, rpos), dim);
            rpos++;
            break;
        case 'B':
        case 'C':
        case 'D':
        case 'F':
        case 'I':
        case 'J':
        case 'S':
        case 'Z':
            rpos++; // base types are already properly read
            break;
        default:
            rpos++;
            // throw new ByteCodeFormatException();
        }
        return res;
    }

    private List<TypeArgumentInfo>[] readMethodSignature(String[] prereadParams,
            List<TypeParameterInfo> listForTypeParams) throws IOException, ByteCodeFormatException {
        @SuppressWarnings("unchecked")
        List<TypeArgumentInfo>[] res = new ArrayList[prereadParams.length];
        String sig = pool[in.readUnsignedShort()];
        if (sig.charAt(0) == '<') {
            listForTypeParams.addAll(readFormalTypeParameters(sig));
        }
        int cur = -1;
        int rpos = sig.indexOf('(') + 1;
        boolean hasReturnValue = false;
        while (!hasReturnValue) {
            cur++;
            if (sig.charAt(rpos) == ')') {
                hasReturnValue = true;
                rpos++; // skip )
            }
            int dim = 0;
            while (sig.charAt(rpos) == '[') {
                dim++;
                rpos++;
            }
            switch (sig.charAt(rpos)) {
            case 'L':
                int lpos = rpos;
                while (sig.charAt(rpos) != ';') {
                    if (sig.charAt(rpos) == '<') {
                        int talpos = rpos;
                        int o = 1;
                        while (o > 0) {
                            rpos++;
                            if (sig.charAt(rpos) == '<') {
                                o++;
                            }
                            if (sig.charAt(rpos) == '>') {
                                o--;
                            }
                        }
                        String targs = sig.substring(talpos, rpos);
                        res[cur] = makeTypeArgs(targs);
                    }
                    rpos++;
                }
                // String typeName = sig.substring(lpos+1,rpos).replace('/','.');
                rpos++; // skip ';'
                break;
            case 'T':
                lpos = rpos;
                while (sig.charAt(rpos) != ';') {
                    rpos++;
                }

                prereadParams[cur] = Naming.toArrayTypeName(sig.substring(lpos + 1, rpos), dim);
                rpos++;
                break;
            case 'B':
            case 'C':
            case 'D':
            case 'F':
            case 'I':
            case 'J':
            case 'S':
            case 'Z':
                rpos++; // base types are already properly read
                break;
            default:
                rpos++;
                // throw new ByteCodeFormatException();
            }
        }

        // if (cur+1 != prereadParams.length) { //<= this may actually happen with enum constructors
        // throw new ByteCodeFormatException();
        // }
        return res;
    }

    private static class ReadClassSignatureResult {
        List<TypeParameterInfo> typeParams;
        List<List<TypeArgumentInfo>> typeArgumentArray;
        List<String> typeNameArray;
    }
}
