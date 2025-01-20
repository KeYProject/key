/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

import recoder.io.*;
import recoder.java.JavaProgramFactory;
import recoder.service.*;

public class DefaultServiceConfiguration extends ServiceConfiguration {

    protected ProjectSettings makeProjectSettings() {
        return new ProjectSettings(this);
    }

    protected ChangeHistory makeChangeHistory() {
        return new ChangeHistory(this);
    }

    protected ProgramFactory makeProgramFactory() {
        return JavaProgramFactory.getInstance();
    }

    protected SourceFileRepository makeSourceFileRepository() {
        return new DefaultSourceFileRepository(this);
    }

    protected ClassFileRepository makeClassFileRepository() {
        return new DefaultClassFileRepository(this);
    }

    protected SourceInfo makeSourceInfo() {
        return new DefaultSourceInfo(this);
    }

    protected ByteCodeInfo makeByteCodeInfo() {
        return new DefaultByteCodeInfo(this);
    }

    protected ImplicitElementInfo makeImplicitElementInfo() {
        return new DefaultImplicitElementInfo(this);
    }

    protected NameInfo makeNameInfo() {
        return new DefaultNameInfo(this);
    }

    protected ConstantEvaluator makeConstantEvaluator() {
        return new DefaultConstantEvaluator(this);
    }
}
