package de.uka.ilkd.key.settings;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

public final class ProofIndependentSMTSettings
        implements de.uka.ilkd.key.settings.Settings, Cloneable {

    private static final String ACTIVE_SOLVER = "[SMTSettings]ActiveSolver";

    private static final String KEY_TIMEOUT = "[SMTSettings]SolverTimeout";


    private static final String PATH_FOR_SMT_TRANSLATION = "[SMTSettings]pathForSMTTranslation";

    private static final String PATH_FOR_TACLET_TRANSLATION =
        "[SMTSettings]pathForTacletTranslation";

    private static final String SHOW_SMT_RES_DIA = "[SMTSettings]showSMTResDialog";


    private static final String PROGRESS_DIALOG_MODE = "[SMTSettings]modeOfProgressDialog";


    private static final String MAX_CONCURRENT_PROCESSES = "[SMTSettings]maxConcurrentProcesses";

    /*
     * The following properties are used to set the bit sizes for bounded counter example
     * generation.
     */
    private static final String INT_BOUND = "[SMTSettings]intBound";
    private static final String HEAP_BOUND = "[SMTSettings]heapBound";
    private static final String FIELD_BOUND = "[SMTSettings]fieldBound";
    private static final String OBJECT_BOUND = "[SMTSettings]objectBound";
    private static final String LOCSET_BOUND = "[SMTSettings]locsetBound";

    private static final String SOLVER_PARAMETERS = "[SMTSettings]solverParametersV1";
    private static final String SOLVER_COMMAND = "[SMTSettings]solverCommand";
    private static final String PROP_TIMEOUT = "[SMTSettings]timeout";
    private static final String SOLVER_CHECK_FOR_SUPPORT = "[SMTSettings]checkForSupport";

    private static final ProofIndependentSMTSettings DEFAULT_DATA =
        new ProofIndependentSMTSettings();

    private static final int DEFAULT_BIT_LENGTH_FOR_CE_GENERATION = 3;

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

    private final Collection<SettingsListener> listeners = new LinkedHashSet<>();

    private SolverTypeCollection activeSolverUnion = SolverTypeCollection.EMPTY_COLLECTION;
    private LinkedList<SolverTypeCollection> solverUnions = new LinkedList<>();
    private LinkedList<SolverTypeCollection> legacyTranslationSolverUnions = new LinkedList<>();

    private boolean checkForSupport = true;

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
        this.showResultsAfterExecution = showResultsAfterExecution;
    }

    public boolean isStoreSMTTranslationToFile() {
        return storeSMTTranslationToFile;
    }

    public void setStoreSMTTranslationToFile(boolean storeSMTTranslationToFile) {
        this.storeSMTTranslationToFile = storeSMTTranslationToFile;
    }

    public boolean isStoreTacletTranslationToFile() {
        return storeTacletTranslationToFile;
    }

    public void setStoreTacletTranslationToFile(boolean storeTacletTranslationToFile) {
        this.storeTacletTranslationToFile = storeTacletTranslationToFile;
    }

    public long getTimeout() {
        return timeout;
    }

    public void setTimeout(long timeout) {
        this.timeout = timeout;
    }

    public ProgressMode getModeOfProgressDialog() {
        return modeOfProgressDialog;
    }

    public void setModeOfProgressDialog(ProgressMode modeOfProgressDialog) {
        this.modeOfProgressDialog = modeOfProgressDialog;
    }

    public String getPathForSMTTranslation() {
        return pathForSMTTranslation;
    }

    public void setPathForSMTTranslation(String pathForSMTTranslation) {
        this.pathForSMTTranslation = pathForSMTTranslation;
    }

    public String getPathForTacletTranslation() {
        return pathForTacletTranslation;
    }

    public void setPathForTacletTranslation(String pathForTacletTranslation) {
        this.pathForTacletTranslation = pathForTacletTranslation;
    }

    public String getActiveSolver() {
        return activeSolver;
    }

    public void setActiveSolver(String activeSolver) {
        this.activeSolver = activeSolver;
    }

    public long getIntBound() {
        return intBound;
    }

    public void setIntBound(long intBound) {
        this.intBound = intBound;
    }

    public long getHeapBound() {
        return heapBound;
    }

    public void setHeapBound(long heapBound) {
        this.heapBound = heapBound;
    }

    public long getSeqBound() {
        return seqBound;
    }

    public void setSeqBound(long seqBound) {
        this.seqBound = seqBound;
    }

    public long getObjectBound() {
        return objectBound;
    }

    public void setObjectBound(long objectBound) {
        this.objectBound = objectBound;
    }

    public long getLocsetBound() {
        return locsetBound;
    }

    public void setLocsetBound(long locsetBound) {
        this.locsetBound = locsetBound;
    }

    public boolean isCheckForSupport() {
        return checkForSupport;
    }

    public void setCheckForSupport(boolean checkForSupport) {
        this.checkForSupport = checkForSupport;
    }

    public enum ProgressMode {
        USER, CLOSE, CLOSE_FIRST
    }

    public int getMaxConcurrentProcesses() {
        return maxConcurrentProcesses;
    }


    public void setMaxConcurrentProcesses(int maxConcurrentProcesses) {
        this.maxConcurrentProcesses = maxConcurrentProcesses;
    }


    public void copy(ProofIndependentSMTSettings data) {
        this.showResultsAfterExecution = data.showResultsAfterExecution;
        this.storeSMTTranslationToFile = data.storeSMTTranslationToFile;
        this.storeTacletTranslationToFile = data.storeTacletTranslationToFile;
        this.timeout = data.timeout;
        this.maxConcurrentProcesses = data.maxConcurrentProcesses;
        this.pathForSMTTranslation = data.pathForSMTTranslation;
        this.pathForTacletTranslation = data.pathForTacletTranslation;
        this.modeOfProgressDialog = data.modeOfProgressDialog;
        this.checkForSupport = data.checkForSupport;
        this.intBound = data.intBound;
        this.heapBound = data.heapBound;
        this.seqBound = data.seqBound;
        this.locsetBound = data.locsetBound;
        this.objectBound = data.objectBound;


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

        for (SolverType type : solverTypes) {
            SettingsConverter.store(props, PROP_TIMEOUT + type.getName(), type.getSolverTimeout());
            SettingsConverter.store(props, SOLVER_PARAMETERS + type.getName(),
                type.getSolverParameters());
            SettingsConverter.store(props, SOLVER_COMMAND + type.getName(),
                type.getSolverCommand());
        }
    }

    public void setActiveSolverUnion(SolverTypeCollection solverUnion) {
        if (activeSolverUnion != solverUnion) {
            activeSolverUnion = solverUnion;
            activeSolver = activeSolverUnion.name();
            fireSettingsChanged();
        }
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
