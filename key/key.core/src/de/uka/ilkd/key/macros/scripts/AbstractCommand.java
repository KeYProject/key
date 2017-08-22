package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.scripts.meta.ArgumentsLifter;
import de.uka.ilkd.key.macros.scripts.meta.DescriptionFacade;
import de.uka.ilkd.key.macros.scripts.meta.ProofScriptArgument;
import de.uka.ilkd.key.proof.Proof;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.logging.Logger;

/**
 * <p><b>Inheritance:</b></p>
 *
 * @param <T>
 * @author Alexander Weigl
 */
public abstract class AbstractCommand<T> implements ProofScriptCommand<T> {
    protected static Logger log = Logger.getLogger(ProofScriptCommand.class.getName());
    protected Proof proof;
    protected Services service;
    protected EngineState state;
    protected AbstractUserInterfaceControl uiControl;

    /**
     * Documentation of this command.
     */
    protected String documentation = null;

    /**
     * ...
     */
    private final Class<T> parameterClazz;

    public AbstractCommand(Class<T> clazz) {
        this.parameterClazz = clazz;
    }

    public List<ProofScriptArgument> getArguments() {
        if (parameterClazz == null)
            return new ArrayList<>();
        return ArgumentsLifter.inferScriptArguments(parameterClazz, this);
    }


    @Override
    public T evaluateArguments(EngineState state, Map<String, String> arguments) throws Exception {
        if (parameterClazz != null) {
            T obj = parameterClazz.newInstance();
            return state.getValueInjector().inject(this, obj, arguments);
        }
        return null;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, T args, EngineState stateMap)
            throws ScriptException, InterruptedException {
        proof = stateMap.getProof();
        service = proof.getServices();
        state = stateMap;
        this.uiControl = uiControl;

        try {
            execute(args);
        } finally {
            //preventing memory leak
            proof = null;
            service = null;
            state = null;
        }
    }

    /**
     * @param args
     * @throws ScriptException
     * @throws InterruptedException
     */
    protected void execute(T args) throws ScriptException, InterruptedException {

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getDocumentation() {
        if (documentation == null) {
            documentation = DescriptionFacade.getDocumentation(this);
        }
        return documentation;
    }
}
