/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

import recoder.io.ClassFileRepository;
import recoder.io.ProjectSettings;
import recoder.io.SourceFileRepository;
import recoder.service.*;

/**
 * A configuration of services that can work together.
 * <p>
 * To exchange a service S1 by a service S2, simply override the corresponding <CODE>makeS</CODE>
 * method.
 * <p>
 * To provide a complete new Service S, add the following code to a subclass of the
 * DefaultServiceConfiguration:
 *
 * <PRE>
 * <p>
 * private S s; protected void makeServices() { super.makeServices(); s =
 * makeS(); } protected void initServices() { super.initServices();
 * s.initialize(this); } protected S makeS() { return new S1(...); } public
 * final S getS() { return s; }
 *
 * </PRE>
 */
public abstract class ServiceConfiguration {

    private ProjectSettings projectSettings;

    private ProgramFactory programFactory;

    private ChangeHistory changeHistory;

    private SourceFileRepository sourceFileRepository;

    private ClassFileRepository classFileRepository;

    private SourceInfo sourceInfo;

    private ByteCodeInfo byteCodeInfo;

    private ImplicitElementInfo implicitElementInfo;

    private NameInfo nameInfo;

    private ConstantEvaluator constantEvaluator;

    public ServiceConfiguration() {
        makeServices();
        initServices();
    }

    /**
     * Called during service initialization: constructs services.
     */
    protected void makeServices() {
        changeHistory = makeChangeHistory();
        projectSettings = makeProjectSettings();
        programFactory = makeProgramFactory();
        sourceFileRepository = makeSourceFileRepository();
        classFileRepository = makeClassFileRepository();
        sourceInfo = makeSourceInfo();
        byteCodeInfo = makeByteCodeInfo();
        nameInfo = makeNameInfo();
        constantEvaluator = makeConstantEvaluator();
        implicitElementInfo = makeImplicitElementInfo();
    }

    /**
     * Called during service initialization: constructs services.
     */
    protected void initServices() {
        changeHistory.initialize(this);
        projectSettings.initialize(this);
        programFactory.initialize(this);
        sourceFileRepository.initialize(this);
        classFileRepository.initialize(this);
        sourceInfo.initialize(this);
        byteCodeInfo.initialize(this);
        implicitElementInfo.initialize(this);
        nameInfo.initialize(this);
        constantEvaluator.initialize(this);
    }

    public final ProjectSettings getProjectSettings() {
        return projectSettings;
    }

    public final ProgramFactory getProgramFactory() {
        return programFactory;
    }

    public final ChangeHistory getChangeHistory() {
        return changeHistory;
    }

    public final SourceFileRepository getSourceFileRepository() {
        return sourceFileRepository;
    }

    public final ClassFileRepository getClassFileRepository() {
        return classFileRepository;
    }

    public final SourceInfo getSourceInfo() {
        return sourceInfo;
    }

    public final ByteCodeInfo getByteCodeInfo() {
        return byteCodeInfo;
    }

    public final ImplicitElementInfo getImplicitElementInfo() {
        return implicitElementInfo;
    }

    public final NameInfo getNameInfo() {
        return nameInfo;
    }

    public final ConstantEvaluator getConstantEvaluator() {
        return constantEvaluator;
    }

    protected abstract ProjectSettings makeProjectSettings();

    protected abstract ChangeHistory makeChangeHistory();

    protected abstract ProgramFactory makeProgramFactory();

    protected abstract SourceFileRepository makeSourceFileRepository();

    protected abstract ClassFileRepository makeClassFileRepository();

    protected abstract SourceInfo makeSourceInfo();

    protected abstract ByteCodeInfo makeByteCodeInfo();

    protected abstract ImplicitElementInfo makeImplicitElementInfo();

    protected abstract NameInfo makeNameInfo();

    protected abstract ConstantEvaluator makeConstantEvaluator();

}
