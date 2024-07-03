/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

// compatible with the byte code standard and with java.lang.reflect.Modifier
public interface AccessFlags {
    int PUBLIC = 0x0001;

    int PRIVATE = 0x0002;

    int PROTECTED = 0x0004;

    int STATIC = 0x0008;

    int FINAL = 0x0010;

    int SUPER = 0x0020; // shared with SYNCHRONIZED

    int SYNCHRONIZED = 0x0020;

    int VOLATILE = 0x0040;

    int BRIDGE = 0x0040; // as of Java 5, shared with BRIDGE

    int TRANSIENT = 0x0080;

    int VARARGS = 0x0080; // as of Java 5, shared with TRANSIENT

    int NATIVE = 0x0100;

    int INTERFACE = 0x0200;

    int ABSTRACT = 0x0400;

    int STRICT = 0x0800;

    int SYNTHETIC = 0x1000; // as of Java 5 (optional flag)

    int ANNOTATION = 0x2000; // as of Java 5

    int ENUM = 0x4000; // as of Java 5


}
