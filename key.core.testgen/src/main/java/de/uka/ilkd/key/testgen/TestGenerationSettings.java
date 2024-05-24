/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.settings.AbstractSettings;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.SettingsConverter;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

import java.io.File;
import java.util.Properties;

public class TestGenerationSettings extends AbstractSettings {
    // region Default Values for option fields
    private static final boolean DEFAULT_APPLYSYMBOLICEX = false;
    private static final int DEFAULT_MAXUNWINDS = 3;
    private static final int DEFAULT_CONCURRENTPROCESSES = 1;
    private static final String DEFAULT_OUTPUTPATH =
            System.getProperty("user.home") + File.separator + "testFiles";
    private static final boolean DEFAULT_REMOVEDUPLICATES = true;
    private static final boolean DEFAULT_USERFL = false;
    private static final Format DEFAULT_USEJUNIT = Format.JUNIT_4;
    private static final boolean DEFAULT_INVARIANTFORALL = true;
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
    private static final String PROP_INCLUDE_POST_CONDITION = "IncludePostCondition";
    private static final String PROP_ONLY_TEST_CLASSES = "onlyTestClasses";

    private static final String CATEGORY = "TestGenSettings";
    // endregion

    // Option fields
    private boolean applySymbolicExecution;
    private int maxUnwinds;
    private String outputPath;
    private boolean removeDuplicates;
    private boolean useRFL;
    private Format format;
    private int concurrentProcesses;
    private boolean invariantForAll;
    private boolean includePostCondition;
    private boolean useRFLAsInternalClass;
    private boolean onlyTestClasses;

    public TestGenerationSettings() {
        applySymbolicExecution = DEFAULT_APPLYSYMBOLICEX;
        maxUnwinds = DEFAULT_MAXUNWINDS;
        outputPath = DEFAULT_OUTPUTPATH;
        removeDuplicates = DEFAULT_REMOVEDUPLICATES;
        useRFL = DEFAULT_USERFL;
        format = Format.JUNIT_4;
        concurrentProcesses = DEFAULT_CONCURRENTPROCESSES;
        invariantForAll = DEFAULT_INVARIANTFORALL;
        includePostCondition = DEFAULT_INCLUDEPOSTCONDITION;
    }

    public TestGenerationSettings(TestGenerationSettings data) {
        applySymbolicExecution = data.applySymbolicExecution;
        maxUnwinds = data.maxUnwinds;
        outputPath = data.outputPath;
        removeDuplicates = data.removeDuplicates;
        format = data.format;
        useRFL = data.useRFL;
        concurrentProcesses = data.concurrentProcesses;
        invariantForAll = data.invariantForAll;
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
        setUseRFL(SettingsConverter.read(props, prefix + PROP_USE_RFL, DEFAULT_USERFL));
        setFormat(Format.valueOf(
                SettingsConverter.read(props, prefix + PROP_USE_JUNIT, DEFAULT_USEJUNIT.name())));
        setConcurrentProcesses(SettingsConverter.read(props,
                prefix + PROP_CONCURRENT_PROCESSES, DEFAULT_CONCURRENTPROCESSES));
        setInvariantForAll(SettingsConverter.read(props,
                prefix + PROP_INVARIANT_FOR_ALL, DEFAULT_INVARIANTFORALL));
        setIncludePostCondition(SettingsConverter.read(props,
                PROP_INCLUDE_POST_CONDITION, DEFAULT_INCLUDEPOSTCONDITION));
        setOnlyTestClasses(SettingsConverter.read(props, PROP_ONLY_TEST_CLASSES, false));
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

    public void setUseRFL(boolean useRFL) {
        var old = this.useRFL;
        this.useRFL = useRFL;
        firePropertyChange(PROP_USE_RFL, old, this.useRFL);

    }

    public void setFormat(Format format) {
        var old = this.format;
        this.format = format;
        firePropertyChange(PROP_USE_JUNIT, old, this.format);
    }

    public boolean isUseRFL() {
        return useRFL;
    }

    public Format getFormat() {
        return format;
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
        SettingsConverter.store(props, prefix + PROP_USE_JUNIT, format);
        SettingsConverter.store(props, prefix + PROP_INCLUDE_POST_CONDITION, includePostCondition);
        SettingsConverter.store(props, prefix + PROP_ONLY_TEST_CLASSES, onlyTestClasses);
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
        setUseRFL(cat.getBool(PROP_USE_RFL, DEFAULT_USERFL));
        setFormat(cat.getEnum(PROP_USE_JUNIT, Format.JUNIT_4));
        setConcurrentProcesses(cat.getInt(PROP_CONCURRENT_PROCESSES, DEFAULT_CONCURRENTPROCESSES));
        setInvariantForAll(cat.getBool(PROP_INVARIANT_FOR_ALL, DEFAULT_INVARIANTFORALL));
        setIncludePostCondition(
                cat.getBool(PROP_INCLUDE_POST_CONDITION, DEFAULT_INCLUDEPOSTCONDITION));
        setOnlyTestClasses(cat.getBool(PROP_ONLY_TEST_CLASSES));
    }

    @Override
    public void writeSettings(Configuration props) {
        var cat = props.getOrCreateSection(CATEGORY);
        cat.set(PROP_ONLY_TEST_CLASSES, onlyTestClasses);
        cat.set(PROP_APPLY_SYMBOLIC_EXECUTION, applySymbolicExecution);
        cat.set(PROP_CONCURRENT_PROCESSES, concurrentProcesses);
        cat.set(PROP_INVARIANT_FOR_ALL, invariantForAll);
        cat.set(PROP_MAX_UWINDS, maxUnwinds);
        cat.set(PROP_OUTPUT_PATH, outputPath);
        cat.set(PROP_REMOVE_DUPLICATES, removeDuplicates);
        cat.set(PROP_USE_RFL, useRFL);
        cat.set(PROP_USE_JUNIT, format);
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

    public boolean isRFLAsInternalClass() {
        return useRFLAsInternalClass;
    }

    public void setRFLAsInternalClass(boolean rflAsInternalClass) {
        var old = this.useRFLAsInternalClass;
        this.useRFLAsInternalClass = rflAsInternalClass;
        changeSupport.firePropertyChange(PROP_ONLY_TEST_CLASSES, old, rflAsInternalClass);

    }

    public void setOnlyTestClasses(boolean onlyTestClasses) {
        var old = this.onlyTestClasses;
        this.onlyTestClasses = onlyTestClasses;
        changeSupport.firePropertyChange(PROP_ONLY_TEST_CLASSES, old, onlyTestClasses);
    }

    public boolean isOnlyTestClasses() {
        return onlyTestClasses;
    }
}
