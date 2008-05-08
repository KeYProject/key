package de;

import java.io.*;

/*attribute_info {
u2 attribute_name_index;
u4 attribute_length;
u1 info[attribute_length];
}*/

class AttributeInfo {
    
     int attrNameIndex;
     byte[] info;

    public AttributeInfo(DataInputStream dis) throws IOException {
        attrNameIndex = dis.readUnsignedShort();
        int attrLength = dis.readInt();
        info = new byte[attrLength];
        dis.read(info);
    }

    public void print(ClassLister classLister) {
        System.out.println("  Attribute " + classLister.getConstant(attrNameIndex));
        int l = Math.min(32, info.length);
        System.out.print("    ");
        for (int i = 0; i < l; i++) {
            System.out.printf("%02x ", ((int)info[i]) & 0xff);
        }
        System.out.println();
    }
    
}

/* field_info {
        u2 access_flags;
        u2 name_index;
        u2 descriptor_index;
        u2 attributes_count;
        attribute_info attributes[attributes_count];
    }
 */

class FieldInfo {

     int accessFlags;
     int nameIndex;
     int descriptorIndex;
    private AttributeInfo[] attributes;

    public FieldInfo(DataInputStream dis) throws IOException {
        accessFlags = dis.readUnsignedShort();
        nameIndex = dis.readUnsignedShort();
        descriptorIndex = dis.readUnsignedShort();
        int attributesCount = dis.readUnsignedShort();
        attributes = new AttributeInfo[attributesCount];
        for (int i = 0; i < attributes.length; i++) {
            attributes[i] = new AttributeInfo(dis);
        }
    }

    public void print(ClassLister classLister) {
        System.out.println("Field " + classLister.getConstant(nameIndex) + ":");
        System.out.printf ("  Access: 0x%x\n", accessFlags);
        System.out.println("  Descriptor: " + classLister.getConstant(descriptorIndex));
        for (AttributeInfo ai : attributes) {
            ai.print(classLister);
        }
    }
    
}

public class ClassLister {
    static class Pair {
        Object fst, snd;

        public Pair(Object fst, Object snd) {
            super();
            this.fst = fst;
            this.snd = snd;
        }

        public String toString() {
            return "{" + fst + ", " + snd + "}";
        }
    }

    private DataInputStream dis;

    private Object[] constantTable;

    private int constCount;

    private int[] constantTypes;

    private int thisIndex;

    private int superIndex;

    private int intfCount;

    private int[] interfaces;

    private int accessFlags;

    private int fieldsCount;

    private FieldInfo[] fields;

    public ClassLister(String arg) throws FileNotFoundException {
        dis = new DataInputStream(new FileInputStream(arg));
    }

    public Object getConstant(int index) {
        return constantTable[index];
    }

    public void read() throws IOException {
        // check the magic
        if (dis.readInt() != 0xCAFEBABE)
            throw new IllegalStateException(".class file w/o magic head");

        // overread version
        dis.readInt();

        // constant table:
        constCount = dis.readUnsignedShort();
        constantTable = new Object[constCount];
        constantTypes = new int[constCount];
        for (int i = 1; i < constCount; i++) {
            byte type = dis.readByte();
            constantTypes[i] = type;
            switch (type) {
            case CONSTANT_Utf8:
                constantTable[i] = dis.readUTF();
                break;
            case CONSTANT_String:
                constantTable[i] = dis.readUnsignedShort();
                break;
            case CONSTANT_Class:
                constantTable[i] = dis.readUnsignedShort();
                break;
            case CONSTANT_Fieldref:
            case CONSTANT_Methodref:
            case CONSTANT_InterfaceMethodref:
            case CONSTANT_NameAndType:
                constantTable[i] = new Pair(dis.readUnsignedShort(), dis
                        .readUnsignedShort());
                break;
            case CONSTANT_Float:
            case CONSTANT_Integer:
                constantTable[i] = dis.readInt();
                break;
            case CONSTANT_Long:
            case CONSTANT_Double:
                constantTable[i] = dis.readLong();
                // so ein Muell!
                i++;
                break;
            }
        }

        // read access flags
        accessFlags = dis.readUnsignedShort();

        // read this_entry:
        thisIndex = dis.readUnsignedShort();
        superIndex = dis.readUnsignedShort();
        intfCount = dis.readUnsignedShort();
        interfaces = new int[intfCount];
        for (int i = 0; i < intfCount; i++) {
            interfaces[i] = dis.readUnsignedShort();
        }
        
        // read fields
        fieldsCount = dis.readUnsignedShort();
        fields = new FieldInfo[fieldsCount];
        for (int i = 0; i < fields.length; i++) {
            fields[i] = new FieldInfo(dis);
        }

    }

    public void print() {
        for (int i = 1; i < constCount; i++) {
            System.err.println("#" + i + " = " + constantTable[i] + " ("
                    + CONSTANT_NAMES[constantTypes[i]] + ")");
        }
        System.out.printf("Access flags: %x\n", accessFlags);
        printClassInfo(thisIndex, "Name of this class");
        printClassInfo(superIndex, "Name of super class");

        for (int i = 0; i < intfCount; i++)
            printClassInfo(interfaces[i], "Implements interface");
        
        for (FieldInfo f : fields) {
            f.print(this);
        }

    }

    private void printClassInfo(int index, String msg) {
        int classNameIndex = (Integer) constantTable[index];
        String className = (String) constantTable[classNameIndex];
        System.out.println(msg + ": " + className + " (" + index + ")");
    }

    /**
     * Tags in constant pool to denote type of constant.
     */
    public final static byte CONSTANT_Utf8 = 1;

    public final static byte CONSTANT_Integer = 3;

    public final static byte CONSTANT_Float = 4;

    public final static byte CONSTANT_Long = 5;

    public final static byte CONSTANT_Double = 6;

    public final static byte CONSTANT_Class = 7;

    public final static byte CONSTANT_Fieldref = 9;

    public final static byte CONSTANT_String = 8;

    public final static byte CONSTANT_Methodref = 10;

    public final static byte CONSTANT_InterfaceMethodref = 11;

    public final static byte CONSTANT_NameAndType = 12;

    public final static String CONSTANT_NAMES[] = { null, "UTF8", null,
            "Integer", "Float", "Long", "Double", "Class", "String",
            "Fieldref", "Methodref", "InterfaceMethodref", "NameAndType" };

    public static void main(String[] args) throws IOException {
        for (String arg : args) {
            ClassLister cl = new ClassLister(arg);
            cl.read();
            cl.print();
        }

    }

}
