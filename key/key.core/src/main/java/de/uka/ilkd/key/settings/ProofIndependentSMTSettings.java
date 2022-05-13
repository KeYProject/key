package de.uka.ilkd.key.settings;

import de.uka.ilkd.key.smt.SolverTypeCollection;
import de.uka.ilkd.key.smt.st.INVISMTSolverType;
import de.uka.ilkd.key.smt.st.SolverType;
import de.uka.ilkd.key.smt.st.SolverTypes;

import javax.annotation.Nullable;
import java.util.*;
import java.util.Map.Entry;

public class ProofIndependentSMTSettings implements de.uka.ilkd.key.settings.Settings, Cloneable {

    private static final String ACTIVE_SOLVER = "[SMTSettings]ActiveSolver";

    private static final String KEY_TIMEOUT = "[SMTSettings]SolverTimeout";


    private static final String PATH_FOR_SMT_TRANSLATION = "[SMTSettings]pathForSMTTranslation";

    private static final String PATH_FOR_TACLET_TRANSLATION = "[SMTSettings]pathForTacletTranslation";

    private static final String SHOW_SMT_RES_DIA = "[SMTSettings]showSMTResDialog";


    private static final String PROGRESS_DIALOG_MODE = "[SMTSettings]modeOfProgressDialog";


    private static final String MAX_CONCURRENT_PROCESSES = "[SMTSettings]maxConcurrentProcesses";

    /* The following properties are used to set the bit sizes for bounded
     * counter example generation.
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

    private static final int DEFAULT_BIT_LENGTH_FOR_CE_GENERATION = 3;

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


    private final Map<SolverType, SolverData> dataOfSolvers = new LinkedHashMap<>();
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

    private Collection<SettingsListener> listeners = new LinkedHashSet<>();

    private SolverTypeCollection activeSolverUnion = SolverTypeCollection.EMPTY_COLLECTION;
    private LinkedList<SolverTypeCollection> solverUnions = new LinkedList<>();
    private LinkedList<SolverTypeCollection> legacyTranslationSolverUnions = new LinkedList<>();

    private boolean checkForSupport = true;


    private ProofIndependentSMTSettings(ProofIndependentSMTSettings data) {
        copy(data);
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


        for (Entry<SolverType, SolverData> entry : data.dataOfSolvers.entrySet()) {
            dataOfSolvers.put(entry.getKey(), entry.getValue().clone());
        }

        solverUnions = new LinkedList<>();
        for (SolverTypeCollection solverUnion : data.solverUnions) {
            solverUnions.add(solverUnion);
        }

        legacyTranslationSolverUnions = new LinkedList<>();
        legacyTranslationSolverUnions.addAll(data.legacyTranslationSolverUnions);
    }


    private static final ProofIndependentSMTSettings DEFAULT_DATA = new ProofIndependentSMTSettings();

    public static ProofIndependentSMTSettings getDefaultSettingsData() {
        return DEFAULT_DATA.clone();
    }

    public Collection<SolverType> getSupportedSolvers() {
        return dataOfSolvers.keySet();
    }

    private ProofIndependentSMTSettings() {
        for (SolverType type : SolverTypes.getSolverTypes()) {
            dataOfSolvers.put(type, new SolverData(type));
        }

        // single solvers with new translation
        solverUnions.add(new SolverTypeCollection("Z3", 1, SolverTypes.Z3_NEW_TL_SOLVER));
        solverUnions.add(new SolverTypeCollection("Z3FP", 1, SolverTypes.Z3_FP_SOLVER));
        solverUnions.add(new SolverTypeCollection("CVC4", 1, SolverTypes.CVC4_NEW_TL_SOLVER));
        solverUnions.add(new SolverTypeCollection("INVISMT", 1, SolverTypes.get(INVISMTSolverType.class)));

        // single solvers with legacy translation
        legacyTranslationSolverUnions.add(new SolverTypeCollection("Z3 Legacy TL", 1, SolverTypes.Z3_SOLVER));
        legacyTranslationSolverUnions.add(new SolverTypeCollection("CVC4", 1, SolverTypes.CVC4_SOLVER));

        // union of all solvers with new translation enabled
        solverUnions.add(new SolverTypeCollection("All solvers", 2,
                SolverTypes.Z3_NEW_TL_SOLVER,
                SolverTypes.CVC4_NEW_TL_SOLVER));

        // all available solvers
        legacyTranslationSolverUnions.add(new SolverTypeCollection("Multiple Solvers", 2, SolverTypes.Z3_SOLVER,
                SolverTypes.Z3_NEW_TL_SOLVER,
                SolverTypes.CVC4_SOLVER));
        legacyTranslationSolverUnions.add(new SolverTypeCollection("Z3 old vs new TL",
                2, SolverTypes.Z3_SOLVER,
                SolverTypes.Z3_NEW_TL_SOLVER));
    }


    public String getCommand(SolverType type) {
        return dataOfSolvers.get(type).getSolverCommand();
    }

    public String getParameters(SolverType type) {
        return dataOfSolvers.get(type).getSolverParameters();
    }

    public void setCommand(SolverType type, String command) {
        dataOfSolvers.get(type).setSolverCommand(command);
    }

    public void setParameters(SolverType type, String parameters) {
        dataOfSolvers.get(type).setSolverParameters(parameters);
    }

    public Collection<SolverData> getDataOfSolvers() {
        return dataOfSolvers.values();
    }

    public @Nullable
    SolverData getSolverData(SolverType type) {
        return dataOfSolvers.get(type);
    }


    public ProofIndependentSMTSettings clone() {
        return new ProofIndependentSMTSettings(this);
    }


    public void readSettings(Properties props) {
        timeout = SettingsConverter.read(props, KEY_TIMEOUT, timeout);
        showResultsAfterExecution = SettingsConverter.read(props, SHOW_SMT_RES_DIA, showResultsAfterExecution);
        pathForSMTTranslation = SettingsConverter.read(props, PATH_FOR_SMT_TRANSLATION, pathForSMTTranslation);
        pathForTacletTranslation = SettingsConverter.read(props, PATH_FOR_TACLET_TRANSLATION, pathForTacletTranslation);
        modeOfProgressDialog = SettingsConverter.read(props, PROGRESS_DIALOG_MODE, modeOfProgressDialog,
                ProgressMode.values());
        maxConcurrentProcesses = SettingsConverter.read(props, MAX_CONCURRENT_PROCESSES, maxConcurrentProcesses);
        checkForSupport = SettingsConverter.read(props, SOLVER_CHECK_FOR_SUPPORT, checkForSupport);
        intBound = SettingsConverter.read(props, INT_BOUND, intBound);
        heapBound = SettingsConverter.read(props, HEAP_BOUND, heapBound);
        seqBound = SettingsConverter.read(props, FIELD_BOUND, seqBound);
        locsetBound = SettingsConverter.read(props, LOCSET_BOUND, locsetBound);
        objectBound = SettingsConverter.read(props, OBJECT_BOUND, objectBound);

        for (SolverData solverData : dataOfSolvers.values()) {
            solverData.readSettings(props);
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

        for (SolverData solverData : dataOfSolvers.values()) {
            solverData.writeSettings(props);
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
        if (activeSolverUnion.isUsable()) {
            return activeSolverUnion;
        }
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

    public static class SolverData {
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

        private void readSettings(Properties props) {
            setSolverParameters(SettingsConverter.read(props,
                    SOLVER_PARAMETERS + getType().getName(), getSolverParameters()));
            setTimeout(SettingsConverter.read(props, PROP_TIMEOUT + getType().getName(), getTimeout()));
            setSolverCommand(SettingsConverter.read(props,
                    SOLVER_COMMAND + getType().getName(), getSolverCommand()));
            getType().setSolverParameters(getSolverParameters());
            getType().setSolverCommand(getSolverCommand());

        }

        private void writeSettings(Properties props) {
            SettingsConverter.store(props, SOLVER_PARAMETERS + getType().getName(), getSolverParameters());
            SettingsConverter.store(props, SOLVER_COMMAND + getType().getName(), getSolverCommand());
            SettingsConverter.store(props, PROP_TIMEOUT + getType().getName(), getTimeout());
            getType().setSolverParameters(getSolverParameters());
            getType().setSolverCommand(getSolverCommand());
        }


        public SolverData clone() {
            return new SolverData(getType(), getSolverCommand(), getSolverParameters(), getTimeout());
        }

        public String toString() {
            return getType().getName();
        }

        public String getSolverParameters() {
            return solverParameters;
        }

        public void setSolverParameters(String solverParameters) {
            this.solverParameters = solverParameters;
        }

        public String getSolverCommand() {
            return solverCommand;
        }

        public void setSolverCommand(String solverCommand) {
            this.solverCommand = solverCommand;
        }

        public SolverType getType() {
            return type;
        }

        public long getTimeout() {
            return timeout;
        }

        public void setTimeout(long timeout) {
            this.timeout = timeout;
        }
    }
}