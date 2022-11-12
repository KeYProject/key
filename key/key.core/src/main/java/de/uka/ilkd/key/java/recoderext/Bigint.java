/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.java.recoderext;

import recoder.abstraction.PrimitiveType;
import recoder.service.ProgramModelInfo;

/**
 * RecodeR extension for JML's \bigint type.
 *
 * @author bruns
 *
 */
public final class Bigint extends PrimitiveType {

    public Bigint(String name, ProgramModelInfo pmi) {
        super(name, pmi);
    }

}
