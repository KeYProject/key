/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;


import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;
import org.jspecify.annotations.NullMarked;

@NullMarked
public class ProofDependentSMTSettings extends AbstractSettings {
    public static final String CATEGORY = "SMTSettings";

    public static final String EXPLICIT_TYPE_HIERARCHY = "explicitTypeHierarchy";
    public static final String INSTANTIATE_NULL_PREDICATES =
        "instantiateHierarchyAssumptions";
    public static final String MAX_GENERIC_SORTS = "maxGenericSorts";
    public static final String TACLET_SELECTION = "SelectedTaclets";
    public static final String USE_BUILT_IN_UNIQUENESS = "UseBuiltUniqueness";
    public static final String USE_UNINTERPRETED_MULTIPLICATION =
        "useUninterpretedMultiplication";
    public static final String USE_CONSTANTS_FOR_BIGSMALL_INTEGERS =
        "useConstantsForBigOrSmallIntegers";
    public static final String INTEGERS_MAXIMUM = "integersMaximum";
    public static final String INTEGERS_MINIMUM = "integersMinimum";
    public static final String INVARIANT_FORALL = "invariantForall";

    private static final String PROP_SUPPORTED_TACLETS = "supportedTaclets";

    private boolean useExplicitTypeHierarchy = false;
    private boolean useNullInstantiation = true;
    private boolean useBuiltInUniqueness = false;
    private boolean useUIMultiplication = true;
    private boolean useConstantsForIntegers = true;
    private boolean invariantForall = false;
    private int maxGenericSorts = 2;
    private int maxInteger = 2147483645;
    private int minInteger = -2147483645;

    private SupportedTaclets supportedTaclets = SupportedTaclets.REFERENCE;

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
        return DEFAULT_DATA.copy();
    }

    public ProofDependentSMTSettings copy() {
        return new ProofDependentSMTSettings(this);
    }


    @Override
    public void readSettings(Configuration props) {
        props = props.getSection(CATEGORY);

        if (props == null)
            return;

        setUseExplicitTypeHierarchy(
            props.getBool(EXPLICIT_TYPE_HIERARCHY, useExplicitTypeHierarchy));
        setUseNullInstantiation(props.getBool(INSTANTIATE_NULL_PREDICATES, useNullInstantiation));
        setUseBuiltInUniqueness(props.getBool(USE_BUILT_IN_UNIQUENESS, useBuiltInUniqueness));
        setMaxGenericSorts(props.getInt(MAX_GENERIC_SORTS, maxGenericSorts));
        setUseUIMultiplication(
            props.getBool(USE_UNINTERPRETED_MULTIPLICATION, useUIMultiplication));
        setUseConstantsForIntegers(
            props.getBool(USE_CONSTANTS_FOR_BIGSMALL_INTEGERS, useConstantsForIntegers));
        setMaxInteger(props.getInt(INTEGERS_MAXIMUM, maxInteger));
        setMinInteger(props.getInt(INTEGERS_MINIMUM, minInteger));
        setInvariantForall(props.getBool(INVARIANT_FORALL, invariantForall));
        supportedTaclets.selectTaclets(
            props.getStringArray(TACLET_SELECTION, supportedTaclets.getNamesOfSelectedTaclets()));

    }

    @Override
    public void writeSettings(Configuration props) {
        props = props.getOrCreateSection(CATEGORY);
        props.set(EXPLICIT_TYPE_HIERARCHY, useExplicitTypeHierarchy);
        props.set(INSTANTIATE_NULL_PREDICATES, useNullInstantiation);
        props.set(MAX_GENERIC_SORTS, maxGenericSorts);
        props.set(TACLET_SELECTION, supportedTaclets.getNamesOfSelectedTaclets());
        props.set(USE_BUILT_IN_UNIQUENESS, useBuiltInUniqueness);
        props.set(USE_UNINTERPRETED_MULTIPLICATION, useUIMultiplication);
        props.set(USE_CONSTANTS_FOR_BIGSMALL_INTEGERS, useConstantsForIntegers);
        props.set(INTEGERS_MAXIMUM, maxInteger);
        props.set(INTEGERS_MINIMUM, minInteger);
        props.set(INVARIANT_FORALL, invariantForall);
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
        this.maxInteger = (int) maxInteger;
        firePropertyChange(INTEGERS_MAXIMUM, old, maxInteger);
    }

    public long getMinInteger() {
        return minInteger;
    }

    public void setMinInteger(long minInteger) {
        var old = this.minInteger;
        this.minInteger = (int) minInteger;
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
}
