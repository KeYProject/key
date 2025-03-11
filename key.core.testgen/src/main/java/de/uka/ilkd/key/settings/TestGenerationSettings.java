/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.io.File;
import java.util.Properties;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public class TestGenerationSettings extends AbstractSettings {
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
    private static final String PROP_APPLY_SYMBOLIC_EXECUTION = "applySymbolicExecution";
    private static final String PROP_MAX_UWINDS = "maxUnwinds";
    private static final String PROP_OUTPUT_PATH = "OutputPath";
    private static final String PROP_REMOVE_DUPLICATES = "RemoveDuplicates";
    private static final String PROP_USE_RFL = "UseRFL";
    private static final String PROP_USE_JUNIT = "UseJUnit";
    private static final String PROP_CONCURRENT_PROCESSES = "ConcurrentProcesses";
    private static final String PROP_INVARIANT_FOR_ALL = "InvariantForAll";
    private static final String PROP_OPENJML_PATH = "OpenJMLPath";
    private static final String PROP_OBJENESIS_PATH = "ObjenesisPath";
    private static final String PROP_INCLUDE_POST_CONDITION =
        "IncludePostCondition";
    private static final String CATEGORY = "TestGenSettings";
    // endregion

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
        applySymbolicExecution = DEFAULT_APPLYSYMBOLICEX;
        maxUnwinds = DEFAULT_MAXUNWINDS;
        outputPath = DEFAULT_OUTPUTPATH;
        removeDuplicates = DEFAULT_REMOVEDUPLICATES;
        useRFL = DEFAULT_USERFL;
        useJunit = DEFAULT_USEJUNIT;
        concurrentProcesses = DEFAULT_CONCURRENTPROCESSES;
        invariantForAll = DEFAULT_INVARIANTFORALL;
        openjmlPath = DEFAULT_OPENJMLPATH;
        objenesisPath = DEFAULT_OBJENESISPATH;
        includePostCondition = DEFAULT_INCLUDEPOSTCONDITION;
    }

    public TestGenerationSettings(TestGenerationSettings data) {
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

    /**
     * @deprecated weigl: This method seems broken. I would expect: clone() = new TGS(this)
     */
    @Deprecated(forRemoval = true)
    public TestGenerationSettings clone(TestGenerationSettings data) {
        return new TestGenerationSettings(data);
    }

    public TestGenerationSettings clone() {
        return new TestGenerationSettings(this);
    }

    public boolean getApplySymbolicExecution() {
        return applySymbolicExecution;
    }

    public void setApplySymbolicExecution(boolean applySymbolicExecution) {
        var old = this.applySymbolicExecution;
        this.applySymbolicExecution = applySymbolicExecution;
        firePropertyChange(PROP_APPLY_SYMBOLIC_EXECUTION, old, this.applySymbolicExecution);
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
        var prefix = "[" + CATEGORY + "]";
        setApplySymbolicExecution(SettingsConverter.read(props,
            prefix + PROP_APPLY_SYMBOLIC_EXECUTION, DEFAULT_APPLYSYMBOLICEX));
        setMaxUnwinds(SettingsConverter.read(props, prefix + PROP_MAX_UWINDS, DEFAULT_MAXUNWINDS));
        setOutputPath(SettingsConverter.read(props, prefix + PROP_OUTPUT_PATH, DEFAULT_OUTPUTPATH));
        setRemoveDuplicates(SettingsConverter.read(props,
            prefix + PROP_REMOVE_DUPLICATES, DEFAULT_REMOVEDUPLICATES));
        setRFL(SettingsConverter.read(props, prefix + PROP_USE_RFL, DEFAULT_USERFL));
        setUseJunit(SettingsConverter.read(props, prefix + PROP_USE_JUNIT, DEFAULT_USEJUNIT));
        setConcurrentProcesses(SettingsConverter.read(props,
            prefix + PROP_CONCURRENT_PROCESSES, DEFAULT_CONCURRENTPROCESSES));
        setInvariantForAll(SettingsConverter.read(props,
            prefix + PROP_INVARIANT_FOR_ALL, DEFAULT_INVARIANTFORALL));
        setOpenjmlPath(
            SettingsConverter.read(props, prefix + PROP_OPENJML_PATH, DEFAULT_OPENJMLPATH));
        setObjenesisPath(SettingsConverter.read(props, PROP_OBJENESIS_PATH, DEFAULT_OBJENESISPATH));
        setIncludePostCondition(SettingsConverter.read(props,
            PROP_INCLUDE_POST_CONDITION, DEFAULT_INCLUDEPOSTCONDITION));
    }

    public boolean removeDuplicates() {
        return removeDuplicates;
    }

    public void setConcurrentProcesses(int concurrentProcesses) {
        var old = this.concurrentProcesses;
        this.concurrentProcesses = concurrentProcesses;
        firePropertyChange(PROP_CONCURRENT_PROCESSES, old, this.concurrentProcesses);
    }

    public void setInvariantForAll(boolean invariantForAll) {
        var old = this.invariantForAll;
        this.invariantForAll = invariantForAll;
        firePropertyChange(PROP_INVARIANT_FOR_ALL, old, this.invariantForAll);
    }

    public void setMaxUnwinds(int maxUnwinds) {
        var old = this.maxUnwinds;
        this.maxUnwinds = maxUnwinds;
        firePropertyChange(PROP_MAX_UWINDS, old, this.maxUnwinds);
    }

    public void setOutputPath(String outputPath) {
        var old = this.outputPath;
        this.outputPath = outputPath;
        firePropertyChange(PROP_OUTPUT_PATH, old, this.outputPath);

    }

    public void setRemoveDuplicates(boolean removeDuplicates) {
        var old = this.removeDuplicates;
        this.removeDuplicates = removeDuplicates;
        firePropertyChange(PROP_REMOVE_DUPLICATES, old, this.removeDuplicates);

    }

    public void setIncludePostCondition(boolean includePostCondition) {
        var old = this.includePostCondition;
        this.includePostCondition = includePostCondition;
        firePropertyChange(PROP_INCLUDE_POST_CONDITION, old, this.includePostCondition);

    }

    public void setRFL(boolean useRFL) {
        var old = this.useRFL;
        this.useRFL = useRFL;
        firePropertyChange(PROP_USE_RFL, old, this.useRFL);

    }

    public void setUseJunit(boolean useJunit) {
        var old = this.useJunit;
        this.useJunit = useJunit;
        firePropertyChange(PROP_USE_JUNIT, old, this.useJunit);

    }

    public String getObjenesisPath() {
        return objenesisPath;
    }

    public void setObjenesisPath(String objenesisPath) {
        var old = this.objenesisPath;
        this.objenesisPath = objenesisPath;
        firePropertyChange(PROP_OBJENESIS_PATH, old, this.objenesisPath);

    }

    public String getOpenjmlPath() {
        return openjmlPath;
    }

    public void setOpenjmlPath(String openjmlPath) {
        var old = this.openjmlPath;
        this.openjmlPath = openjmlPath;
        firePropertyChange(PROP_OPENJML_PATH, old, this.openjmlPath);
    }

    public boolean useRFL() {
        return useRFL;
    }

    public boolean useJunit() {
        return useJunit;
    }


    @Override
    public void writeSettings(Properties props) {
        var prefix = "[" + CATEGORY + "]";
        SettingsConverter.store(props, prefix + PROP_APPLY_SYMBOLIC_EXECUTION,
            applySymbolicExecution);
        SettingsConverter.store(props, prefix + PROP_CONCURRENT_PROCESSES, concurrentProcesses);
        SettingsConverter.store(props, prefix + PROP_INVARIANT_FOR_ALL, invariantForAll);
        SettingsConverter.store(props, prefix + PROP_MAX_UWINDS, maxUnwinds);
        SettingsConverter.store(props, prefix + PROP_OUTPUT_PATH, outputPath);
        SettingsConverter.store(props, prefix + PROP_REMOVE_DUPLICATES, removeDuplicates);
        SettingsConverter.store(props, prefix + PROP_USE_RFL, useRFL);
        SettingsConverter.store(props, prefix + PROP_USE_JUNIT, useJunit);
        SettingsConverter.store(props, prefix + PROP_OPENJML_PATH, openjmlPath);
        SettingsConverter.store(props, prefix + PROP_OBJENESIS_PATH, objenesisPath);
        SettingsConverter.store(props, prefix + PROP_INCLUDE_POST_CONDITION, includePostCondition);
    }

    @Override
    public void readSettings(Configuration props) {
        var cat = props.getSection(CATEGORY);
        if (cat == null)
            return;
        setApplySymbolicExecution(
            cat.getBool(PROP_APPLY_SYMBOLIC_EXECUTION, DEFAULT_APPLYSYMBOLICEX));
        setMaxUnwinds(cat.getInt(PROP_MAX_UWINDS, DEFAULT_MAXUNWINDS));
        setOutputPath(cat.getString(PROP_OUTPUT_PATH, DEFAULT_OUTPUTPATH));
        setRemoveDuplicates(cat.getBool(PROP_REMOVE_DUPLICATES, DEFAULT_REMOVEDUPLICATES));
        setRFL(cat.getBool(PROP_USE_RFL, DEFAULT_USERFL));
        setUseJunit(cat.getBool(PROP_USE_JUNIT, DEFAULT_USEJUNIT));
        setConcurrentProcesses(cat.getInt(PROP_CONCURRENT_PROCESSES, DEFAULT_CONCURRENTPROCESSES));
        setInvariantForAll(cat.getBool(PROP_INVARIANT_FOR_ALL, DEFAULT_INVARIANTFORALL));
        setOpenjmlPath(cat.getString(PROP_OPENJML_PATH, DEFAULT_OPENJMLPATH));
        setObjenesisPath(cat.getString(PROP_OBJENESIS_PATH, DEFAULT_OBJENESISPATH));
        setIncludePostCondition(
            cat.getBool(PROP_INCLUDE_POST_CONDITION, DEFAULT_INCLUDEPOSTCONDITION));
    }

    @Override
    public void writeSettings(Configuration props) {
        var cat = props.getOrCreateSection(CATEGORY);

        cat.set(PROP_APPLY_SYMBOLIC_EXECUTION, applySymbolicExecution);
        cat.set(PROP_CONCURRENT_PROCESSES, concurrentProcesses);
        cat.set(PROP_INVARIANT_FOR_ALL, invariantForAll);
        cat.set(PROP_MAX_UWINDS, maxUnwinds);
        cat.set(PROP_OUTPUT_PATH, outputPath);
        cat.set(PROP_REMOVE_DUPLICATES, removeDuplicates);
        cat.set(PROP_USE_RFL, useRFL);
        cat.set(PROP_USE_JUNIT, useJunit);
        cat.set(PROP_OPENJML_PATH, openjmlPath);
        cat.set(PROP_OBJENESIS_PATH, objenesisPath);
        cat.set(PROP_INCLUDE_POST_CONDITION, includePostCondition);
    }

    public void set(TestGenerationSettings settings) {
        Properties p = new Properties();
        settings.writeSettings(p);
        readSettings(p);
    }


    private static @Nullable TestGenerationSettings instance;

    public static @NonNull TestGenerationSettings getInstance() {
        if (instance == null) {
            instance = new TestGenerationSettings();
            ProofIndependentSettings.DEFAULT_INSTANCE.addSettings(instance);
        }
        return instance;
    }
}
