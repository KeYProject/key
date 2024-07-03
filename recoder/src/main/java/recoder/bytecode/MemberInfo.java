/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.bytecode;

import java.util.List;

import recoder.abstraction.ClassType;
import recoder.abstraction.Member;

public abstract class MemberInfo extends ByteCodeElement implements Member {

    protected ClassFile parent;

    List<AnnotationUseInfo> annotations;

    public MemberInfo(int accessFlags, String name, ClassFile parent) {
        super(accessFlags, name);
        setParent(parent);
    }

    public ClassFile getParent() {
        return parent;
    }

    public void setParent(ClassFile parent) {
        this.parent = parent;
    }

    public ClassType getContainingClassType() {
        return service.getContainingClassType(this);
    }

    /**
     * @return a list of annotations
     */
    public List<AnnotationUseInfo> getAnnotations() {
        return annotations;
    }

    void setAnnotations(List<AnnotationUseInfo> annotations) {
        this.annotations = annotations;
    }
}
