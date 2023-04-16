// This file is part of the RECODER library and protected by the LGPL.

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
