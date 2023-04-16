// This file is part of the RECODER library and protected by the LGPL.
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import recoder.ProgramFactory;
import recoder.service.SourceInfo;

public class SchemaCrossReferenceServiceConfiguration
        extends KeYCrossReferenceServiceConfiguration {

    public SchemaCrossReferenceServiceConfiguration(KeYRecoderExcHandler keh) {
        super(keh);
    }

    /** we need another factory for some new program elements */
    protected ProgramFactory makeProgramFactory() {
        return SchemaJavaProgramFactory.getInstance();
    }

    /**
     * The cross reference source info is a subclass of the source info, so this class simply
     * overrides the source info factory method.
     */
    protected SourceInfo makeSourceInfo() {
        return new SchemaCrossReferenceSourceInfo(this);
    }


}
