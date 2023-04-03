package de.uka.ilkd.key.settings;

import java.io.File;
import java.util.Collection;
import java.util.EventObject;
import java.util.LinkedHashSet;
import java.util.Properties;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

public class TestGenerationSettings implements Settings, Cloneable {
    // region Default Values for option fields
    private static final boolean DEFAULT_APPLYSYMBOLICEX = false;
    private static final int DEFAULT_MAXUNWINDS = 3;
    private static final int DEFAULT_CONCURRENTPROCESSES = 1;
    private static final String DEFAULT_OUTPUTPATH =
        System.getProperty("user.home") + File.separator + "testFiles";
    private static final boolean DEFAULT_REMOVEDUPLICATES = true;
    private static final boolean DEFAULT_USERFL = false;
    private static final boolean DEFAULT_USEJUNIT = false;
    private static final boolean DEFAULT_INVARIANTFORALL = true;
    private static final String DEFAULT_OPENJMLPATH = ".";
    private static final String DEFAULT_OBJENESISPATH = ".";
    private static final boolean DEFAULT_INCLUDEPOSTCONDITION = false;
    // endregion

    // region property names
    private static final String PROP_APPLY_SYMBOLIC_EXECUTION =
        "[TestGenSettings]applySymbolicExecution";
    private static final String PROP_MAX_UWINDS = "[TestGenSettings]maxUnwinds";
    private static final String PROP_OUTPUT_PATH = "[TestGenSettings]OutputPath";
    private static final String PROP_REMOVE_DUPLICATES = "[TestGenSettings]RemoveDuplicates";
    private static final String PROP_USE_RFL = "[TestGenSettings]UseRFL";
    private static final String PROP_USE_JUNIT = "[TestGenSettings]UseJUnit";
    private static final String PROP_CONCURRENT_PROCESSES = "[TestGenSettings]ConcurrentProcesses";
    private static final String PROP_INVARIANT_FOR_ALL = "[TestGenSettings]InvariantForAll";
    private static final String PROP_OPENJML_PATH = "[TestGenSettings]OpenJMLPath";
    private static final String PROP_OBJENESIS_PATH = "[TestGenSettings]ObjenesisPath";
    private static final String PROP_INCLUDE_POST_CONDITION =
        "[TestGenSettings]IncludePostCondition";
    // endregion

    private final Collection<SettingsListener> listeners;
    // Option fields
    private boolean applySymbolicExecution;
    private int maxUnwinds;
    private String outputPath;
    private String openjmlPath;
    private String objenesisPath;
    private boolean removeDuplicates;
    private boolean useRFL;
    private boolean useJunit;
    private int concurrentProcesses;
    private boolean invariantForAll;
    private boolean includePostCondition;


    public TestGenerationSettings() {
        listeners = new LinkedHashSet<>();
        applySymbolicExecution = TestGenerationSettings.DEFAULT_APPLYSYMBOLICEX;
        maxUnwinds = TestGenerationSettings.DEFAULT_MAXUNWINDS;
        outputPath = TestGenerationSettings.DEFAULT_OUTPUTPATH;
        removeDuplicates = TestGenerationSettings.DEFAULT_REMOVEDUPLICATES;
        useRFL = TestGenerationSettings.DEFAULT_USERFL;
        useJunit = TestGenerationSettings.DEFAULT_USEJUNIT;
        concurrentProcesses = TestGenerationSettings.DEFAULT_CONCURRENTPROCESSES;
        invariantForAll = TestGenerationSettings.DEFAULT_INVARIANTFORALL;
        openjmlPath = DEFAULT_OPENJMLPATH;
        objenesisPath = DEFAULT_OBJENESISPATH;
        includePostCondition = DEFAULT_INCLUDEPOSTCONDITION;
    }

    public TestGenerationSettings(TestGenerationSettings data) {
        listeners = new LinkedHashSet<>();
        listeners.addAll(data.listeners);
        applySymbolicExecution = data.applySymbolicExecution;
        maxUnwinds = data.maxUnwinds;
        outputPath = data.outputPath;
        removeDuplicates = data.removeDuplicates;
        useJunit = data.useJunit;
        useRFL = data.useRFL;
        concurrentProcesses = data.concurrentProcesses;
        invariantForAll = data.invariantForAll;
        openjmlPath = data.openjmlPath;
        objenesisPath = data.objenesisPath;
        includePostCondition = data.includePostCondition;

    }

    @Override
    public void addSettingsListener(SettingsListener l) {
        listeners.add(l);
    }

    @Override
    public void removeSettingsListener(SettingsListener l) {
        listeners.remove(l);
    }

    // FIXME weigl: This method seems broken. I would expect: clone() = new TGS(this)
    public TestGenerationSettings clone(TestGenerationSettings data) {
        return new TestGenerationSettings(data);
    }

    public void fireSettingsChanged() {
        for (final SettingsListener aListenerList : listeners) {
            aListenerList.settingsChanged(new EventObject(this));
        }
    }

    public boolean getApplySymbolicExecution() {
        return applySymbolicExecution;
    }

    public void setApplySymbolicExecution(boolean applySymbolicExecution) {
        this.applySymbolicExecution = applySymbolicExecution;
    }

    public int getMaximalUnwinds() {
        return maxUnwinds;
    }

    public int getNumberOfProcesses() {
        return concurrentProcesses;
    }

    public String getOutputFolderPath() {
        return outputPath;
    }

    public boolean invariantForAll() {
        return invariantForAll;
    }

    public boolean includePostCondition() {
        return includePostCondition;
    }

    @Override
    public void readSettings(Properties props) {
        applySymbolicExecution =
            SettingsConverter.read(props, TestGenerationSettings.PROP_APPLY_SYMBOLIC_EXECUTION,
                TestGenerationSettings.DEFAULT_APPLYSYMBOLICEX);
        maxUnwinds = SettingsConverter.read(props, TestGenerationSettings.PROP_MAX_UWINDS,
            TestGenerationSettings.DEFAULT_MAXUNWINDS);
        outputPath = SettingsConverter.read(props, TestGenerationSettings.PROP_OUTPUT_PATH,
            TestGenerationSettings.DEFAULT_OUTPUTPATH);
        removeDuplicates =
            SettingsConverter.read(props, TestGenerationSettings.PROP_REMOVE_DUPLICATES,
                TestGenerationSettings.DEFAULT_REMOVEDUPLICATES);
        useRFL = SettingsConverter.read(props, TestGenerationSettings.PROP_USE_RFL,
            TestGenerationSettings.DEFAULT_USERFL);
        useJunit = SettingsConverter.read(props, TestGenerationSettings.PROP_USE_JUNIT,
            TestGenerationSettings.DEFAULT_USEJUNIT);
        concurrentProcesses =
            SettingsConverter.read(props, TestGenerationSettings.PROP_CONCURRENT_PROCESSES,
                TestGenerationSettings.DEFAULT_CONCURRENTPROCESSES);
        invariantForAll =
            SettingsConverter.read(props, TestGenerationSettings.PROP_INVARIANT_FOR_ALL,
                TestGenerationSettings.DEFAULT_INVARIANTFORALL);
        openjmlPath = SettingsConverter.read(props, TestGenerationSettings.PROP_OPENJML_PATH,
            TestGenerationSettings.DEFAULT_OPENJMLPATH);

        objenesisPath = SettingsConverter.read(props, TestGenerationSettings.PROP_OBJENESIS_PATH,
            TestGenerationSettings.DEFAULT_OBJENESISPATH);

        includePostCondition =
            SettingsConverter.read(props, TestGenerationSettings.PROP_INCLUDE_POST_CONDITION,
                TestGenerationSettings.DEFAULT_INCLUDEPOSTCONDITION);
    }

    public boolean removeDuplicates() {
        return removeDuplicates;
    }

    public void setConcurrentProcesses(int concurrentProcesses) {
        this.concurrentProcesses = concurrentProcesses;
    }

    public void setInvariantForAll(boolean invariantForAll) {
        this.invariantForAll = invariantForAll;
    }

    public void setMaxUnwinds(int maxUnwinds) {
        this.maxUnwinds = maxUnwinds;
    }

    public void setOutputPath(String outputPath) {
        this.outputPath = outputPath;
    }

    public void setRemoveDuplicates(boolean removeDuplicates) {
        this.removeDuplicates = removeDuplicates;
    }

    public void setIncludePostCondition(boolean includePostCondition) {
        this.includePostCondition = includePostCondition;
    }

    public void setRFL(boolean useRFL) {
        this.useRFL = useRFL;
    }

    public void setUseJunit(boolean useJunit) {
        this.useJunit = useJunit;
    }

    public String getObjenesisPath() {
        return objenesisPath;
    }

    public void setObjenesisPath(String objenesisPath) {
        this.objenesisPath = objenesisPath;
    }

    public String getOpenjmlPath() {
        return openjmlPath;
    }

    public void setOpenjmlPath(String openjmlPath) {
        this.openjmlPath = openjmlPath;
    }

    public boolean useRFL() {
        return useRFL;
    }

    public boolean useJunit() {
        return useJunit;
    }


    @Override
    public void writeSettings(Properties props) {
        SettingsConverter.store(props, TestGenerationSettings.PROP_APPLY_SYMBOLIC_EXECUTION,
            applySymbolicExecution);
        SettingsConverter.store(props, TestGenerationSettings.PROP_CONCURRENT_PROCESSES,
            concurrentProcesses);
        SettingsConverter.store(props, TestGenerationSettings.PROP_INVARIANT_FOR_ALL,
            invariantForAll);
        SettingsConverter.store(props, TestGenerationSettings.PROP_MAX_UWINDS, maxUnwinds);
        SettingsConverter.store(props, TestGenerationSettings.PROP_OUTPUT_PATH, outputPath);
        SettingsConverter.store(props, TestGenerationSettings.PROP_REMOVE_DUPLICATES,
            removeDuplicates);
        SettingsConverter.store(props, TestGenerationSettings.PROP_USE_RFL, useRFL);
        SettingsConverter.store(props, TestGenerationSettings.PROP_USE_JUNIT, useJunit);
        SettingsConverter.store(props, TestGenerationSettings.PROP_OPENJML_PATH, openjmlPath);
        SettingsConverter.store(props, TestGenerationSettings.PROP_OBJENESIS_PATH, objenesisPath);
        SettingsConverter.store(props, TestGenerationSettings.PROP_INCLUDE_POST_CONDITION,
            includePostCondition);
    }

    public void set(TestGenerationSettings settings) {
        Properties p = new Properties();
        settings.writeSettings(p);
        readSettings(p);
    }


    private static @Nullable TestGenerationSettings instance;

    public static @Nonnull TestGenerationSettings getInstance() {
        if (instance == null) {
            instance = new TestGenerationSettings();
            ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(instance);
        }
        return instance;
    }
}
