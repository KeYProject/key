/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.abstraction;

import java.util.List;

import recoder.service.ProgramModelInfo;

/**
 * @author Tobias Gutzmann
 */
public interface TypeParameter extends ClassType {
    String getParameterName();

    int getBoundCount();

    String getBoundName(int boundidx);

    List<? extends TypeArgument> getBoundTypeArguments(int boundidx);

    // public Member getDeclaringMember();
    ClassType getContainingClassType();

    /**
     * Helper class that implements the equals() method for implementing classes.
     *
     * @see recoder.java.declaration.TypeParameterDeclaration
     * @see recoder.bytecode.TypeParameterInfo
     */
    class EqualsImplementor {
        public static boolean equals(TypeParameter t1, Object o) {
            if (t1 == o) {
                return true;
            }
            if (!(o instanceof TypeParameter)) {
                return false;
            }
            TypeParameter t2 = (TypeParameter) o;
            ClassType c1 = t1.getContainingClassType();
            ClassType c2 = t2.getContainingClassType();

            if (c1 == null || c2 == null) {
                return false; // generic method; covered by direct comparison!
            }
            if (c1 == c2) {
                return false; // otherwise, t1 == t2, too
            }
            ProgramModelInfo pmi = c1.getProgramModelInfo();
            if (pmi.isSubtype(c1, c2)) {
                List<ClassType> tl = c1.getSupertypes();
                for (ClassType superCT : tl) {
                    if (superCT.getTypeParameters() == null) {
                        continue;
                    }
                    if (!(superCT instanceof ParameterizedType)) {
                        continue;
                    }
                    TypeParameter tryUpwards = null;
                    {
                        // find ridx
                        int ridx = -1;
                        List<? extends TypeArgument> rl =
                            ((ParameterizedType) superCT).getTypeArgs();
                        for (int j = 0; j < rl.size(); j++) {
                            TypeArgument ta = rl.get(j);
                            if (ta.getTypeName().equals(t1.getName())) {
                                ridx = j;
                                break;
                            }
                        }
                        if (ridx == -1) {
                            continue;
                        }
                        tryUpwards = superCT.getTypeParameters().get(ridx);
                    }
                    if (equals(tryUpwards, t2)) {
                        return true;
                    }
                }
            } else if (pmi.isSubtype(c2, c1)) {
                return equals((TypeParameter) o, t1);
            } /* else false */
            return false;
        }

    }
}
