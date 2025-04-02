/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import recoder.ModelException;
import recoder.abstraction.ProgramModelElement;
import recoder.service.ProgramModelInfo;

public abstract class ByteCodeElement implements ProgramModelElement {

    protected int accessFlags;

    protected String name;

    protected ProgramModelInfo service;

    public ByteCodeElement() {
        super();
    }

    public ByteCodeElement(int accessFlags) {
        this.accessFlags = accessFlags;
    }

    public ByteCodeElement(int accessFlags, String name) {
        setName(name);
        this.accessFlags = accessFlags;
    }

    /**
     * Returns the name of the byte code element. Strings are interned so that they can be compared
     * by identity.
     */
    public final String getName() {
        return name;
    }

    final void setName(String name) {
        this.name = name.intern();
    }

    public abstract String getTypeName();

    public final int getAccessFlags() {
        return accessFlags;
    }

    public void setAccessFlags(int accessFlags) {
        this.accessFlags = accessFlags;
    }

    public boolean isAbstract() {
        return (accessFlags & ABSTRACT) != 0;
    }

    public boolean isFinal() {
        return (accessFlags & FINAL) != 0;
    }

    public boolean isStatic() {
        return (accessFlags & STATIC) != 0;
    }

    public boolean isPrivate() {
        return (accessFlags & PRIVATE) != 0;
    }

    public boolean isProtected() {
        return (accessFlags & PROTECTED) != 0;
    }

    public boolean isPublic() {
        return (accessFlags & PUBLIC) != 0;
    }

    public boolean isStrictFp() {
        return (accessFlags & STRICT) != 0;
    }

    public boolean isNative() {
        return (accessFlags & NATIVE) != 0;
    }

    public boolean isSynchronized() {
        return (accessFlags & SYNCHRONIZED) != 0;
    }

    public ProgramModelInfo getProgramModelInfo() {
        return service;
    }

    public void setProgramModelInfo(ProgramModelInfo service) {
        this.service = service;
    }

    public void validate() throws ModelException {
        // not checked yet
    }

}
