package de.uka.ilkd.key.java.recoderext;

import recoder.abstraction.PrimitiveType;
import recoder.service.ProgramModelInfo;

/**
 * RecodeR extension for JML's \bigint type.
 * @author bruns
 *
 */
public final class Bigint extends PrimitiveType {

    public Bigint(String name, ProgramModelInfo pmi) {
        super(name, pmi);
    }

}
