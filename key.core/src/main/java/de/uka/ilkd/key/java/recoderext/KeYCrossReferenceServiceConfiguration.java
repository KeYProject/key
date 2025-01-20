/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.java.KeYProgModelInfo;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.io.SourceFileRepository;
import recoder.service.KeYCrossReferenceSourceInfo;
import recoder.service.NameInfo;
import recoder.service.SourceInfo;

public class KeYCrossReferenceServiceConfiguration extends CrossReferenceServiceConfiguration {

    protected KeYProgModelInfo kpmi = null;

    public KeYCrossReferenceServiceConfiguration(KeYRecoderExcHandler keh) {
        super(); // initialises servConf
        // better not: it might add to the input path of recoder
        // getProjectSettings().ensureSystemClassesAreInPath();
        assert keh != null : "The exception handler must not be null";
        getProjectSettings().setErrorHandler(keh);
    }

    public KeYCrossReferenceServiceConfiguration(KeYProgModelInfo kpmi) {
        this(kpmi.getExceptionHandler());
        this.kpmi = kpmi;
    }

    protected ProgramFactory makeProgramFactory() {
        return ProofJavaProgramFactory.getInstance();
    }

    /**
     * The cross reference source info is a subclass of the source info, so this class simply
     * overrides the source info factory method.
     */
    protected SourceInfo makeSourceInfo() {
        return new KeYCrossReferenceSourceInfo(this);
    }

    protected SourceFileRepository makeSourceFileRepository() {
        return new KeYCrossReferenceSourceFileRepository(this);
    }

    protected NameInfo makeNameInfo() {
        return new KeYCrossReferenceNameInfo(this);
    }

    public KeYProgModelInfo getKeYProgModelInfo() {
        return kpmi;
    }
}
