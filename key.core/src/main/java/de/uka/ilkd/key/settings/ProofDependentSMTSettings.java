/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;


import java.util.Properties;

import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;


public class ProofDependentSMTSettings extends AbstractSettings {

    public static final String EXPLICIT_TYPE_HIERARCHY = "[SMTSettings]explicitTypeHierarchy";
    public static final String INSTANTIATE_NULL_PREDICATES =
        "[SMTSettings]instantiateHierarchyAssumptions";
    public static final String MAX_GENERIC_SORTS = "[SMTSettings]maxGenericSorts";
    public static final String TACLET_SELECTION = "[SMTSettings]SelectedTaclets";
    public static final String USE_BUILT_IN_UNIQUENESS = "[SMTSettings]UseBuiltUniqueness";
    public static final String USE_UNINTERPRETED_MULTIPLICATION =
        "[SMTSettings]useUninterpretedMultiplication";
    public static final String USE_CONSTANTS_FOR_BIGSMALL_INTEGERS =
        "[SMTSettings]useConstantsForBigOrSmallIntegers";
    public static final String INTEGERS_MAXIMUM = "[SMTSettings]integersMaximum";
    public static final String INTEGERS_MINIMUM = "[SMTSettings]integersMinimum";
    public static final String INVARIANT_FORALL = "[SMTSettings]invariantForall";

    public static final String PROP_LEGACY_TRANSLATION = "[SMTSettings]legacyTranslation";
    private static final String PROP_SUPPORTED_TACLETS = "supportedTaclets";

    private boolean useExplicitTypeHierarchy = false;
    private boolean useNullInstantiation = true;
    private boolean useBuiltInUniqueness = false;
    private boolean useUIMultiplication = true;
    private boolean useConstantsForIntegers = true;
    private boolean invariantForall = false;
    private int maxGenericSorts = 2;
    private long maxInteger = 2147483645;
    private long minInteger = -2147483645;
    private boolean useLegacyTranslation = false;


    private SupportedTaclets supportedTaclets;

    private ProofDependentSMTSettings() {
        setSupportedTaclets(SupportedTaclets.REFERENCE);
    }

    private ProofDependentSMTSettings(ProofDependentSMTSettings data) {
        copy(data);
    }

    public void copy(ProofDependentSMTSettings data) {
        setSupportedTaclets(
            new SupportedTaclets(data.supportedTaclets.getNamesOfSelectedTaclets()));
        setUseExplicitTypeHierarchy(data.useExplicitTypeHierarchy);
        setUseNullInstantiation(data.useNullInstantiation);
        setMaxGenericSorts(data.maxGenericSorts);
        setUseBuiltInUniqueness(data.useBuiltInUniqueness);
        setUseUIMultiplication(data.useUIMultiplication);
        setUseConstantsForIntegers(data.useConstantsForIntegers);
        setMaxInteger(data.maxInteger);
        setMinInteger(data.minInteger);
        setInvariantForall(data.invariantForall);
    }


    private static final ProofDependentSMTSettings DEFAULT_DATA = new ProofDependentSMTSettings();

    public static ProofDependentSMTSettings getDefaultSettingsData() {
        return DEFAULT_DATA.clone();
    }


    @Override
    public ProofDependentSMTSettings clone() {
        return new ProofDependentSMTSettings(this);
    }


    @Override
    public void readSettings(Properties props) {
        setUseExplicitTypeHierarchy(
            SettingsConverter.read(props, EXPLICIT_TYPE_HIERARCHY, useExplicitTypeHierarchy));
        setUseNullInstantiation(
            SettingsConverter.read(props, INSTANTIATE_NULL_PREDICATES, useNullInstantiation));
        setUseBuiltInUniqueness(
            SettingsConverter.read(props, USE_BUILT_IN_UNIQUENESS, useBuiltInUniqueness));
        setMaxGenericSorts(SettingsConverter.read(props, MAX_GENERIC_SORTS, maxGenericSorts));
        setUseUIMultiplication(
            SettingsConverter.read(props, USE_UNINTERPRETED_MULTIPLICATION, useUIMultiplication));
        setUseConstantsForIntegers(
            SettingsConverter.read(props, USE_CONSTANTS_FOR_BIGSMALL_INTEGERS,
                useConstantsForIntegers));

        setMaxInteger(SettingsConverter.read(props, INTEGERS_MAXIMUM, maxInteger));
        setMinInteger(SettingsConverter.read(props, INTEGERS_MINIMUM, minInteger));
        setInvariantForall(SettingsConverter.read(props, INVARIANT_FORALL, invariantForall));
        supportedTaclets.selectTaclets(SettingsConverter.read(props, TACLET_SELECTION,
            supportedTaclets.getNamesOfSelectedTaclets()));
    }

    @Override
    public void writeSettings(Properties props) {
        SettingsConverter.store(props, EXPLICIT_TYPE_HIERARCHY, useExplicitTypeHierarchy);
        SettingsConverter.store(props, INSTANTIATE_NULL_PREDICATES, useNullInstantiation);
        SettingsConverter.store(props, MAX_GENERIC_SORTS, maxGenericSorts);
        SettingsConverter.store(props, TACLET_SELECTION,
            supportedTaclets.getNamesOfSelectedTaclets());
        SettingsConverter.store(props, USE_BUILT_IN_UNIQUENESS, useBuiltInUniqueness);
        SettingsConverter.store(props, USE_UNINTERPRETED_MULTIPLICATION, useUIMultiplication);
        SettingsConverter.store(props, USE_CONSTANTS_FOR_BIGSMALL_INTEGERS,
            useConstantsForIntegers);
        SettingsConverter.store(props, INTEGERS_MAXIMUM, maxInteger);
        SettingsConverter.store(props, INTEGERS_MINIMUM, minInteger);
        SettingsConverter.store(props, INVARIANT_FORALL, invariantForall);
    }

    public boolean isUseExplicitTypeHierarchy() {
        return useExplicitTypeHierarchy;
    }

    public void setUseExplicitTypeHierarchy(boolean useExplicitTypeHierarchy) {
        var old = this.useExplicitTypeHierarchy;
        this.useExplicitTypeHierarchy = useExplicitTypeHierarchy;
        firePropertyChange(EXPLICIT_TYPE_HIERARCHY, old, this.useExplicitTypeHierarchy);
    }

    public boolean isUseNullInstantiation() {
        return useNullInstantiation;
    }

    public void setUseNullInstantiation(boolean useNullInstantiation) {
        var old = this.useNullInstantiation;
        this.useNullInstantiation = useNullInstantiation;
        firePropertyChange(INSTANTIATE_NULL_PREDICATES, old, this.useNullInstantiation);
    }

    public boolean isUseBuiltInUniqueness() {
        return useBuiltInUniqueness;
    }

    public void setUseBuiltInUniqueness(boolean useBuiltInUniqueness) {
        var old = this.useBuiltInUniqueness;
        this.useBuiltInUniqueness = useBuiltInUniqueness;
        firePropertyChange(USE_BUILT_IN_UNIQUENESS, old, useBuiltInUniqueness);
    }

    public boolean isUseUIMultiplication() {
        return useUIMultiplication;
    }

    public void setUseUIMultiplication(boolean useUIMultiplication) {
        var old = this.useUIMultiplication;
        this.useUIMultiplication = useUIMultiplication;
        firePropertyChange(USE_UNINTERPRETED_MULTIPLICATION, old, useUIMultiplication);
    }

    public boolean isUseConstantsForIntegers() {
        return useConstantsForIntegers;
    }

    public void setUseConstantsForIntegers(boolean useConstantsForIntegers) {
        var old = this.useConstantsForIntegers;
        this.useConstantsForIntegers = useConstantsForIntegers;
        firePropertyChange(USE_CONSTANTS_FOR_BIGSMALL_INTEGERS, old, useConstantsForIntegers);
    }

    public boolean isInvariantForall() {
        return invariantForall;
    }

    public void setInvariantForall(boolean invariantForall) {
        var old = this.invariantForall;
        this.invariantForall = invariantForall;
        firePropertyChange(INVARIANT_FORALL, old, invariantForall);
    }

    public int getMaxGenericSorts() {
        return maxGenericSorts;
    }

    public void setMaxGenericSorts(int maxGenericSorts) {
        var old = this.maxGenericSorts;
        this.maxGenericSorts = maxGenericSorts;
        firePropertyChange(MAX_GENERIC_SORTS, old, maxGenericSorts);
    }

    public long getMaxInteger() {
        return maxInteger;
    }

    public void setMaxInteger(long maxInteger) {
        var old = this.maxInteger;
        this.maxInteger = maxInteger;
        firePropertyChange(INTEGERS_MAXIMUM, old, maxInteger);
    }

    public long getMinInteger() {
        return minInteger;
    }

    public void setMinInteger(long minInteger) {
        var old = this.minInteger;
        this.minInteger = minInteger;
        firePropertyChange(INTEGERS_MINIMUM, old, minInteger);
    }

    public SupportedTaclets getSupportedTaclets() {
        return supportedTaclets;
    }

    public void setSupportedTaclets(SupportedTaclets supportedTaclets) {
        var old = this.supportedTaclets;
        this.supportedTaclets = supportedTaclets;
        firePropertyChange(PROP_SUPPORTED_TACLETS, old, supportedTaclets);
    }

    public boolean isUseLegacyTranslation() {
        return useLegacyTranslation;
    }

    public void setUseLegacyTranslation(boolean useLegacyTranslation) {
        var old = this.useLegacyTranslation;
        this.useLegacyTranslation = useLegacyTranslation;
        firePropertyChange(PROP_LEGACY_TRANSLATION, old, useLegacyTranslation);
    }
}
