/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

public final class ProofIndependentSMTSettings
        extends AbstractSettings {

    public static final String ACTIVE_SOLVER = "[SMTSettings]ActiveSolver";
    public static final String KEY_TIMEOUT = "[SMTSettings]SolverTimeout";
    public static final String PATH_FOR_SMT_TRANSLATION = "[SMTSettings]pathForSMTTranslation";
    public static final String PATH_FOR_TACLET_TRANSLATION =
        "[SMTSettings]pathForTacletTranslation";
    public static final String SHOW_SMT_RES_DIA = "[SMTSettings]showSMTResDialog";
    public static final String PROGRESS_DIALOG_MODE = "[SMTSettings]modeOfProgressDialog";
    public static final String MAX_CONCURRENT_PROCESSES = "[SMTSettings]maxConcurrentProcesses";

    /*
     * The following properties are used to set the bit sizes for bounded counter example
     * generation.
     */
    public static final String INT_BOUND = "[SMTSettings]intBound";
    public static final String HEAP_BOUND = "[SMTSettings]heapBound";
    public static final String FIELD_BOUND = "[SMTSettings]fieldBound";
    public static final String OBJECT_BOUND = "[SMTSettings]objectBound";
    public static final String LOCSET_BOUND = "[SMTSettings]locsetBound";

    public static final String SOLVER_PARAMETERS = "[SMTSettings]solverParametersV1";
    public static final String SOLVER_COMMAND = "[SMTSettings]solverCommand";
    public static final String PROP_TIMEOUT = "[SMTSettings]timeout";
    public static final String SOLVER_CHECK_FOR_SUPPORT = "[SMTSettings]checkForSupport";
    public static final String SOLVER_ENABLED_ON_LOAD = "[SMTSettings]enableWhenLoading";

    private static final ProofIndependentSMTSettings DEFAULT_DATA =
        new ProofIndependentSMTSettings();

    private static final int DEFAULT_BIT_LENGTH_FOR_CE_GENERATION = 3;
    public static final String PROP_SOLVER_UNION = "activeSolverUnion";
    public static final String PROP_SHOW_RESULT_AFTER_EXECUTION =
        "PROP_SHOW_RESULT_AFTER_EXECUTION";
    public static final String PROP_STORE_SMT_TRANSLATION_FILE = "PROP_STORE_SMT_TRANSLATION_FILE";
    public static final String PROP_STORE_TACLET_TRANSLATION_FILE =
        "PROP_STORE_TACLET_TRANSLATION_FILE";

    private final Collection<SolverType> solverTypes = new LinkedList<>();
    private boolean showResultsAfterExecution = false;
    private boolean storeSMTTranslationToFile = false;
    private boolean storeTacletTranslationToFile = false;

    private long timeout = 2000;
    private int maxConcurrentProcesses = 2;

    private ProgressMode modeOfProgressDialog = ProgressMode.USER;

    private String pathForSMTTranslation = "";
    private String pathForTacletTranslation = "";
    private String activeSolver = "";


    private long intBound = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;
    private long heapBound = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;
    private long seqBound = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;
    private long objectBound = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;
    private long locsetBound = DEFAULT_BIT_LENGTH_FOR_CE_GENERATION;

    private SolverTypeCollection activeSolverUnion = SolverTypeCollection.EMPTY_COLLECTION;
    private LinkedList<SolverTypeCollection> solverUnions = new LinkedList<>();
    private LinkedList<SolverTypeCollection> legacyTranslationSolverUnions = new LinkedList<>();

    private boolean checkForSupport = true;
    private boolean enableOnLoad = true;

    private ProofIndependentSMTSettings(ProofIndependentSMTSettings data) {
        copy(data);
    }

    /**
     * Creates a new ProofIndependentSettings object with the default solvers created by
     * {@link SolverTypes#getSolverTypes()}.
     */
    private ProofIndependentSMTSettings() {
        // load solver props from standard directory, see PathConfig
        Collection<SolverType> legacyTypes = SolverTypes.getLegacySolvers();
        Collection<SolverType> nonLegacyTypes = SolverTypes.getSolverTypes();
        solverTypes.addAll(nonLegacyTypes);
        nonLegacyTypes.removeAll(legacyTypes);
        // Z3_CE solver should not be a usable solver union or part of any as it is
        // treated separately.
        for (SolverType type : nonLegacyTypes.stream().filter(t -> t != SolverTypes.Z3_CE_SOLVER)
                .collect(Collectors.toList())) {
            solverUnions.add(new SolverTypeCollection(type.getName(), 1, type));
        }

        // single solvers with legacy translation
        for (SolverType type : legacyTypes) {
            legacyTranslationSolverUnions.add(new SolverTypeCollection(type.getName(), 1, type));
        }
    }

    public boolean isShowResultsAfterExecution() {
        return showResultsAfterExecution;
    }

    public void setShowResultsAfterExecution(boolean showResultsAfterExecution) {
        var old = this.showResultsAfterExecution;
        this.showResultsAfterExecution = showResultsAfterExecution;
        firePropertyChange(PROP_SHOW_RESULT_AFTER_EXECUTION, old, this.showResultsAfterExecution);

    }

    public boolean isStoreSMTTranslationToFile() {
        return storeSMTTranslationToFile;
    }

    public void setStoreSMTTranslationToFile(boolean storeSMTTranslationToFile) {
        var old = this.storeSMTTranslationToFile;
        this.storeSMTTranslationToFile = storeSMTTranslationToFile;
        firePropertyChange(PROP_STORE_SMT_TRANSLATION_FILE, old, this.storeSMTTranslationToFile);

    }

    public boolean isStoreTacletTranslationToFile() {
        return storeTacletTranslationToFile;
    }

    public void setStoreTacletTranslationToFile(boolean storeTacletTranslationToFile) {
        var old = this.storeTacletTranslationToFile;
        this.storeTacletTranslationToFile = storeTacletTranslationToFile;
        firePropertyChange(PROP_STORE_TACLET_TRANSLATION_FILE, old,
            this.storeTacletTranslationToFile);

    }

    public long getTimeout() {
        return timeout;
    }

    public void setTimeout(long timeout) {
        var old = this.timeout;
        this.timeout = timeout;
        firePropertyChange(PROP_TIMEOUT, old, this.timeout);

    }

    public ProgressMode getModeOfProgressDialog() {
        return modeOfProgressDialog;
    }

    public void setModeOfProgressDialog(ProgressMode modeOfProgressDialog) {
        var old = this.modeOfProgressDialog;
        this.modeOfProgressDialog = modeOfProgressDialog;
        firePropertyChange(PROGRESS_DIALOG_MODE, old, this.modeOfProgressDialog);

    }

    public String getPathForSMTTranslation() {
        return pathForSMTTranslation;
    }

    public void setPathForSMTTranslation(String pathForSMTTranslation) {
        var old = this.pathForSMTTranslation;
        this.pathForSMTTranslation = pathForSMTTranslation;
        firePropertyChange(PATH_FOR_SMT_TRANSLATION, old, this.pathForSMTTranslation);

    }

    public String getPathForTacletTranslation() {
        return pathForTacletTranslation;
    }

    public void setPathForTacletTranslation(String pathForTacletTranslation) {
        var old = this.pathForTacletTranslation;
        this.pathForTacletTranslation = pathForTacletTranslation;
        firePropertyChange(PATH_FOR_TACLET_TRANSLATION, old, this.pathForTacletTranslation);

    }

    public String getActiveSolver() {
        return activeSolver;
    }

    public void setActiveSolver(String activeSolver) {
        var old = this.activeSolver;
        this.activeSolver = activeSolver;
        firePropertyChange(ACTIVE_SOLVER, old, this.activeSolver);

    }

    public long getIntBound() {
        return intBound;
    }

    public void setIntBound(long intBound) {
        var old = this.intBound;
        this.intBound = intBound;
        firePropertyChange(INT_BOUND, old, this.intBound);

    }

    public long getHeapBound() {
        return heapBound;
    }

    public void setHeapBound(long heapBound) {
        var old = this.heapBound;
        this.heapBound = heapBound;
        firePropertyChange(HEAP_BOUND, old, this.heapBound);

    }

    public long getSeqBound() {
        return seqBound;
    }

    public void setSeqBound(long seqBound) {
        var old = this.seqBound;
        this.seqBound = seqBound;
        firePropertyChange(FIELD_BOUND, old, this.seqBound);

    }

    public long getObjectBound() {
        return objectBound;
    }

    public void setObjectBound(long objectBound) {
        var old = this.objectBound;
        this.objectBound = objectBound;
        firePropertyChange(OBJECT_BOUND, old, this.objectBound);

    }

    public long getLocsetBound() {
        return locsetBound;
    }

    public void setLocsetBound(long locsetBound) {
        var old = this.locsetBound;
        this.locsetBound = locsetBound;
        firePropertyChange(LOCSET_BOUND, old, this.locsetBound);

    }

    public boolean isCheckForSupport() {
        return checkForSupport;
    }

    public void setCheckForSupport(boolean checkForSupport) {
        var old = this.checkForSupport;
        this.checkForSupport = checkForSupport;
        firePropertyChange(SOLVER_CHECK_FOR_SUPPORT, old, this.checkForSupport);
    }

    public enum ProgressMode {
        USER, CLOSE, CLOSE_FIRST
    }

    private final Map<SolverType, SolverData> dataOfSolvers = new LinkedHashMap<>();

    public int getMaxConcurrentProcesses() {
        return maxConcurrentProcesses;
    }


    public void setMaxConcurrentProcesses(int maxConcurrentProcesses) {
        var old = this.maxConcurrentProcesses;
        this.maxConcurrentProcesses = maxConcurrentProcesses;
        firePropertyChange(MAX_CONCURRENT_PROCESSES, old, this.maxConcurrentProcesses);

    }

    public boolean isEnableOnLoad() {
        return enableOnLoad;
    }

    public void setEnableOnLoad(boolean enableOnLoad) {
        this.enableOnLoad = enableOnLoad;
    }

    public void copy(ProofIndependentSMTSettings data) {
        setShowResultsAfterExecution(data.showResultsAfterExecution);
        setStoreSMTTranslationToFile(data.storeSMTTranslationToFile);
        setStoreTacletTranslationToFile(data.storeTacletTranslationToFile);
        setTimeout(data.timeout);
        setMaxConcurrentProcesses(data.maxConcurrentProcesses);
        setPathForSMTTranslation(data.pathForSMTTranslation);
        setPathForTacletTranslation(data.pathForTacletTranslation);
        setModeOfProgressDialog(data.modeOfProgressDialog);
        setCheckForSupport(data.checkForSupport);
        setIntBound(data.intBound);
        setHeapBound(data.heapBound);
        setSeqBound(data.seqBound);
        setLocsetBound(data.locsetBound);
        setObjectBound(data.objectBound);
        setEnableOnLoad(data.enableOnLoad);


        solverTypes.addAll(data.solverTypes);

        solverUnions = new LinkedList<>();
        solverUnions.addAll(data.solverUnions);

        legacyTranslationSolverUnions = new LinkedList<>();
        legacyTranslationSolverUnions.addAll(data.legacyTranslationSolverUnions);
    }

    public static ProofIndependentSMTSettings getDefaultSettingsData() {
        return DEFAULT_DATA.clone();
    }

    public boolean containsSolver(SolverType type) {
        return solverTypes.contains(type);
    }

    public String getCommand(SolverType type) {
        return type.getSolverCommand();
    }

    public long getSolverTimeout(SolverType type) {
        return type.getSolverTimeout();
    }

    public String getParameters(SolverType type) {
        return type.getSolverParameters();
    }

    public void setCommand(SolverType type, String command) {
        type.setSolverCommand(command);
    }

    public void setParameters(SolverType type, String parameters) {
        type.setSolverParameters(parameters);
    }

    public ProofIndependentSMTSettings clone() {
        return new ProofIndependentSMTSettings(this);
    }

    public void readSettings(Properties props) {
        timeout = SettingsConverter.read(props, KEY_TIMEOUT, timeout);
        showResultsAfterExecution =
            SettingsConverter.read(props, SHOW_SMT_RES_DIA, showResultsAfterExecution);
        pathForSMTTranslation =
            SettingsConverter.read(props, PATH_FOR_SMT_TRANSLATION, pathForSMTTranslation);
        pathForTacletTranslation =
            SettingsConverter.read(props, PATH_FOR_TACLET_TRANSLATION, pathForTacletTranslation);
        modeOfProgressDialog = SettingsConverter.read(props, PROGRESS_DIALOG_MODE,
            modeOfProgressDialog, ProgressMode.values());
        maxConcurrentProcesses =
            SettingsConverter.read(props, MAX_CONCURRENT_PROCESSES, maxConcurrentProcesses);
        checkForSupport = SettingsConverter.read(props, SOLVER_CHECK_FOR_SUPPORT, checkForSupport);
        intBound = SettingsConverter.read(props, INT_BOUND, intBound);
        heapBound = SettingsConverter.read(props, HEAP_BOUND, heapBound);
        seqBound = SettingsConverter.read(props, FIELD_BOUND, seqBound);
        locsetBound = SettingsConverter.read(props, LOCSET_BOUND, locsetBound);
        objectBound = SettingsConverter.read(props, OBJECT_BOUND, objectBound);
        enableOnLoad = SettingsConverter.read(props, SOLVER_ENABLED_ON_LOAD, enableOnLoad);

        for (SolverType type : solverTypes) {
            type.setSolverTimeout(SettingsConverter.read(props, PROP_TIMEOUT + type.getName(),
                type.getDefaultSolverTimeout()));
            type.setSolverParameters(SettingsConverter.read(props,
                SOLVER_PARAMETERS + type.getName(), type.getDefaultSolverParameters()));
            type.setSolverCommand(SettingsConverter.read(props, SOLVER_COMMAND + type.getName(),
                type.getDefaultSolverCommand()));
        }
    }

    public void writeSettings(Properties props) {
        SettingsConverter.store(props, KEY_TIMEOUT, timeout);
        SettingsConverter.store(props, SHOW_SMT_RES_DIA, showResultsAfterExecution);
        SettingsConverter.store(props, PROGRESS_DIALOG_MODE, modeOfProgressDialog);
        SettingsConverter.store(props, PATH_FOR_SMT_TRANSLATION, pathForSMTTranslation);
        SettingsConverter.store(props, PATH_FOR_TACLET_TRANSLATION, pathForTacletTranslation);
        SettingsConverter.store(props, ACTIVE_SOLVER, activeSolver);
        SettingsConverter.store(props, MAX_CONCURRENT_PROCESSES, maxConcurrentProcesses);
        SettingsConverter.store(props, SOLVER_CHECK_FOR_SUPPORT, checkForSupport);
        SettingsConverter.store(props, INT_BOUND, intBound);
        SettingsConverter.store(props, HEAP_BOUND, heapBound);
        SettingsConverter.store(props, OBJECT_BOUND, objectBound);
        SettingsConverter.store(props, FIELD_BOUND, seqBound);
        SettingsConverter.store(props, LOCSET_BOUND, locsetBound);
        SettingsConverter.store(props, SOLVER_ENABLED_ON_LOAD, enableOnLoad);

        for (SolverType type : solverTypes) {
            SettingsConverter.store(props, PROP_TIMEOUT + type.getName(), type.getSolverTimeout());
            SettingsConverter.store(props, SOLVER_PARAMETERS + type.getName(),
                type.getSolverParameters());
            SettingsConverter.store(props, SOLVER_COMMAND + type.getName(),
                type.getSolverCommand());
        }
    }

    public void setActiveSolverUnion(SolverTypeCollection solverUnion) {
        var oldActiveSolverUnion = activeSolverUnion;
        activeSolverUnion = solverUnion;
        firePropertyChange(PROP_SOLVER_UNION, oldActiveSolverUnion, activeSolver);
        setActiveSolver(activeSolverUnion.name());
    }

    public SolverTypeCollection computeActiveSolverUnion() {
        // if there is already a solver union configured, return that
        if (activeSolverUnion.isUsable()) {
            return activeSolverUnion;
        }
        // otherwise, first try the default solver: Z3
        Optional<SolverTypeCollection> z3 = solverUnions.stream()
                .filter(x -> x.name().equals("Z3")).findFirst();
        if (z3.isPresent() && z3.get().isUsable()) {
            setActiveSolverUnion(z3.get());
            return z3.get();
        }
        // failing that, any usable solver is accepted...
        for (SolverTypeCollection solverUnion : solverUnions) {
            if (solverUnion.isUsable()) {
                setActiveSolverUnion(solverUnion);
                return solverUnion;
            }
        }
        setActiveSolverUnion(SolverTypeCollection.EMPTY_COLLECTION);
        return SolverTypeCollection.EMPTY_COLLECTION;
    }


    public Collection<SolverTypeCollection> getUsableSolverUnions(boolean experimental) {
        LinkedList<SolverTypeCollection> unions = new LinkedList<>();
        for (SolverTypeCollection union : getSolverUnions(experimental)) {
            if (union.isUsable()) {
                unions.add(union);
            }
        }
        return unions;
    }

    public Collection<SolverTypeCollection> getSolverUnions(boolean experimental) {
        LinkedList<SolverTypeCollection> res = new LinkedList<>(solverUnions);
        if (experimental) {
            res.addAll(legacyTranslationSolverUnions);
        }
        return res;
    }

    public static class SolverData extends AbstractSettings {
        private String solverParameters = "";
        private String solverCommand = "";
        private long timeout = -1;
        private final SolverType type;

        public SolverData(SolverType type) {
            this(type, type.getDefaultSolverCommand(), type.getDefaultSolverParameters());
        }

        private SolverData(SolverType type, String command, String parameters) {
            this(type, command, parameters, -1);
        }

        public SolverData(SolverType type, String command, String parameters, long timeout) {
            this.type = type;
            setSolverCommand(command);
            setSolverParameters(parameters);
            setTimeout(timeout);
        }

        @Override
        public void readSettings(Properties props) {
            setSolverParameters(SettingsConverter.read(props,
                SOLVER_PARAMETERS + getType().getName(), getSolverParameters()));
            setTimeout(
                SettingsConverter.read(props, PROP_TIMEOUT + getType().getName(), getTimeout()));
            setSolverCommand(SettingsConverter.read(props,
                SOLVER_COMMAND + getType().getName(), getSolverCommand()));
            getType().setSolverParameters(getSolverParameters());
            getType().setSolverCommand(getSolverCommand());

        }

        @Override
        public void writeSettings(Properties props) {
            SettingsConverter.store(props, SOLVER_PARAMETERS + getType().getName(),
                getSolverParameters());
            SettingsConverter.store(props, SOLVER_COMMAND + getType().getName(),
                getSolverCommand());
            SettingsConverter.store(props, PROP_TIMEOUT + getType().getName(), getTimeout());
            getType().setSolverParameters(getSolverParameters());
            getType().setSolverCommand(getSolverCommand());
        }


        public SolverData clone() {
            return new SolverData(getType(), getSolverCommand(), getSolverParameters(),
                getTimeout());
        }

        public String toString() {
            return getType().getName();
        }

        public String getSolverParameters() {
            return solverParameters;
        }

        public void setSolverParameters(String solverParameters) {
            var old = this.solverParameters;
            this.solverParameters = solverParameters;
            firePropertyChange(SOLVER_PARAMETERS, old, this.solverParameters);

        }

        public String getSolverCommand() {
            return solverCommand;
        }

        public void setSolverCommand(String solverCommand) {
            var old = this.solverCommand;
            this.solverCommand = solverCommand;
            firePropertyChange(SOLVER_COMMAND, old, this.solverCommand);

        }

        public SolverType getType() {
            return type;
        }

        public long getTimeout() {
            return timeout;
        }

        public void setTimeout(long timeout) {
            var old = this.timeout;
            this.timeout = timeout;
            firePropertyChange(KEY_TIMEOUT, old, this.timeout);
        }
    }
}
