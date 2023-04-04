package de.uka.ilkd.key.settings;


import java.util.Collection;
import java.util.EventObject;
import java.util.LinkedHashSet;
import java.util.Properties;

import de.uka.ilkd.key.taclettranslation.assumptions.SupportedTaclets;



public class ProofDependentSMTSettings implements de.uka.ilkd.key.settings.Settings, Cloneable {

    private static final String EXPLICIT_TYPE_HIERARCHY = "[SMTSettings]explicitTypeHierarchy";

    private static final String INSTANTIATE_NULL_PREDICATES =
        "[SMTSettings]instantiateHierarchyAssumptions";


    private static final String MAX_GENERIC_SORTS = "[SMTSettings]maxGenericSorts";


    private static final String TACLET_SELECTION = "[SMTSettings]SelectedTaclets";

    private static final String USE_BUILT_IN_UNIQUENESS = "[SMTSettings]UseBuiltUniqueness";

    private static final String USE_UNINTERPRETED_MULTIPLICATION =
        "[SMTSettings]useUninterpretedMultiplication";

    private static final String USE_CONSTANTS_FOR_BIGSMALL_INTEGERS =
        "[SMTSettings]useConstantsForBigOrSmallIntegers";

    private static final String INTEGERS_MAXIMUM = "[SMTSettings]integersMaximum";
    private static final String INTEGERS_MINIMUM = "[SMTSettings]integersMinimum";

    private static final String INVARIANT_FORALL = "[SMTSettings]invariantForall";

    private final Collection<SettingsListener> listeners = new LinkedHashSet<>();

    // FIXME Why are these fields public?!
    public boolean useExplicitTypeHierarchy = false;
    public boolean useNullInstantiation = true;
    public boolean useBuiltInUniqueness = false;
    public boolean useUIMultiplication = true;
    public boolean useConstantsForIntegers = true;
    public boolean invariantForall = false;
    public int maxGenericSorts = 2;
    public long maxInteger = 2147483645;
    public long minInteger = -2147483645;
    // TODO js: could be used once the new translation is working
    // public boolean useLegacyTranslation = false;



    public SupportedTaclets supportedTaclets;

    private ProofDependentSMTSettings() {

        supportedTaclets = SupportedTaclets.REFERENCE;
    }

    private ProofDependentSMTSettings(ProofDependentSMTSettings data) {
        copy(data);
    }

    public void copy(ProofDependentSMTSettings data) {
        supportedTaclets = new SupportedTaclets(data.supportedTaclets.getNamesOfSelectedTaclets());
        this.useExplicitTypeHierarchy = data.useExplicitTypeHierarchy;
        this.useNullInstantiation = data.useNullInstantiation;
        this.maxGenericSorts = data.maxGenericSorts;
        this.useBuiltInUniqueness = data.useBuiltInUniqueness;
        this.useUIMultiplication = data.useUIMultiplication;
        this.useConstantsForIntegers = data.useConstantsForIntegers;
        this.maxInteger = data.maxInteger;
        this.minInteger = data.minInteger;
        this.invariantForall = data.invariantForall;

    }


    private static final ProofDependentSMTSettings DEFAULT_DATA = new ProofDependentSMTSettings();

    public static ProofDependentSMTSettings getDefaultSettingsData() {
        return DEFAULT_DATA.clone();
    }



    @Override
    public ProofDependentSMTSettings clone() {
        return new ProofDependentSMTSettings(this);
    }


    public void readSettings(Properties props) {

        useExplicitTypeHierarchy =
            SettingsConverter.read(props, EXPLICIT_TYPE_HIERARCHY, useExplicitTypeHierarchy);
        useNullInstantiation =
            SettingsConverter.read(props, INSTANTIATE_NULL_PREDICATES, useNullInstantiation);
        useBuiltInUniqueness =
            SettingsConverter.read(props, USE_BUILT_IN_UNIQUENESS, useBuiltInUniqueness);

        maxGenericSorts = SettingsConverter.read(props, MAX_GENERIC_SORTS, maxGenericSorts);

        useUIMultiplication =
            SettingsConverter.read(props, USE_UNINTERPRETED_MULTIPLICATION, useUIMultiplication);
        useConstantsForIntegers = SettingsConverter.read(props, USE_CONSTANTS_FOR_BIGSMALL_INTEGERS,
            useConstantsForIntegers);

        maxInteger = SettingsConverter.read(props, INTEGERS_MAXIMUM, maxInteger);
        minInteger = SettingsConverter.read(props, INTEGERS_MINIMUM, minInteger);

        invariantForall = SettingsConverter.read(props, INVARIANT_FORALL, invariantForall);

        supportedTaclets.selectTaclets(SettingsConverter.read(props, TACLET_SELECTION,
            supportedTaclets.getNamesOfSelectedTaclets()));

    }

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


    public void fireSettingsChanged() {
        for (SettingsListener aListenerList : listeners) {
            aListenerList.settingsChanged(new EventObject(this));
        }

    }

    @Override
    public void addSettingsListener(SettingsListener l) {
        listeners.add(l);

    }

    @Override
    public void removeSettingsListener(SettingsListener l) {
        listeners.remove(l);
    }



}
