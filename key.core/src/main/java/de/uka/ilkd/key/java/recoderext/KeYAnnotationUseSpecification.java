/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.declaration.AnnotationUseSpecification;
import recoder.java.reference.TypeReference;

// HACK: This class is declared due to a bug in recoder causing a stack overflow when
// deepClone@AnnotationUseSpecification is called
public class KeYAnnotationUseSpecification extends AnnotationUseSpecification {

    /**
     *
     */
    private static final long serialVersionUID = 2163251956161988258L;

    public KeYAnnotationUseSpecification() {
        super();
    }

    public KeYAnnotationUseSpecification(TypeReference tr) {
        super(tr);
    }

    public KeYAnnotationUseSpecification deepClone() {
        return new KeYAnnotationUseSpecification(getTypeReference());
    }

}
