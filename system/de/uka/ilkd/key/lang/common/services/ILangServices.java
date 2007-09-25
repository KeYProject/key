package de.uka.ilkd.key.lang.common.services;

import java.io.IOException;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.common.metaop.BaseMetaOp;
import de.uka.ilkd.key.lang.common.program.BaseVariable;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.program.IVariable;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.lang.common.programsv.IVariableProgramSVSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Programming language specific services.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface ILangServices {

        /**
         * Creates a new instance (the state is no copied).
         * 
         * @param env
         *                environment to use
         * @return
         */
        public ILangServices newInstance(ILangServicesEnv env);

        /**
         * Creates a copy of the language services.
         * 
         * @param env
         *                environment to use
         * @return
         */
        public ILangServices copy(ILangServicesEnv env);

        /**
         * Introduces standard sorts and symbols into the namespaces.
         * 
         * @param sortNS
         * @param symbolNS
         */
        void init(Namespace sortNS, Namespace symbolNS);

        /**
         * Lazily builds a symbol with given name if it has not been built
         * before. Should be called after the initialization.
         * 
         * @param sortNS
         * @param symbolNS
         * @param sortName
         * @return
         */
        void lazyBuildSort(Namespace sortNS, Namespace symbolNS, Name sortName);

        /**
         * Lazily builds a symbol with given name if it has not been built
         * before. Should be called after the initialization.
         * 
         * @param sortNS
         * @param symbolNS
         * @param symbolName
         * @return
         */
        void lazyBuildSymbol(Namespace sortNS, Namespace symbolNS,
                        Name symbolName);

        /**
         * Loads the program. Populates the namespaces with new sorts and
         * related symbols. Should be called after the initialization. Should be
         * called at most once per language services.
         * 
         * @param path
         *                path of the program source
         * @param sortNS
         * @param symbolNS
         * 
         * @throws IOException
         * @throws ConvertException
         */
        void loadProgram(Namespace sortNS, Namespace symbolNS, String path)
                        throws IOException, ConvertException;

        /**
         * Loads program statements as a program element. Should be called after
         * the initialization. May populate the namespaces with new sorts and
         * related symbols.
         * 
         * @param sortNS
         * @param symbolNS
         * @param schemaVariableNS
         *                possibly <code>null</code>
         * @param programVariableNS
         *                possibly <code>null</code>
         * @param code
         * 
         * @return
         * 
         * @throws ConvertException
         */
        IProgramElement loadStatements(Namespace sortNS, Namespace symbolNS,
                        Namespace schemaVariableNS,
                        Namespace programVariableNS, String code)
                        throws ConvertException;

        /**
         * Converts program element to a term, if possible. Returns
         * <code>null</code> if that is not possible.
         * 
         * @param sortNS
         * @param symbolNS
         * @param programElement
         * @return
         */
        Term convertProgramElementToTerm(Namespace sortNS, Namespace symbolNS,
                        IProgramElement programElement);

        /**
         * Builds a program variable with given name and type pair for given
         * variable programSV sort.
         * 
         * @param programSVSort
         * @param name
         * @param typePair
         * @return
         */
        BaseVariable buildVariable(IVariableProgramSVSort programSVSort,
                        ProgramElementName name, KeYJavaType typePair);

        /**
         * Builds a program variable with given name and type pair for given
         * prototype variable.
         * 
         * @param prototypeVariable
         * @param programSVSort
         * @param name
         * @param typePair
         * @return
         */
        BaseVariable copyVariable(IVariable prototypeVariable,
                        ProgramElementName name, KeYJavaType typePair);

        /**
         * Creates variable name proposal based on the type pair.
         * 
         * @param typePair
         * @return
         */
        String getVariableNameProposal(KeYJavaType typePair);

        /**
         * Looks up {@link BaseProgramSVSort} with given name. Returns
         * <code>null</code> if not found.
         * 
         * @param name
         * @return
         */
        BaseProgramSVSort getProgramSVSort(Name name);

        /**
         * Looks up {@link BaseMetaOp} with given name. Returns
         * <code>null</code> if not found.
         * 
         * @param name
         * @return
         */
        BaseMetaOp getMetaOp(Name name);

        /**
         * Exception thrown when program instantiation fails.
         */
        public static class InstantiationException extends RuntimeException {
                public InstantiationException(String message) {
                        super(message);
                }

                public InstantiationException() {
                }
        }

        /**
         * Instantiates the program element with schema variable instantiations.
         * 
         * @param sortNS
         * @param symbolNS
         * @param programElement
         * @param svInst
         * 
         * @return
         */
        IProgramElement instantiateProgram(Namespace sortNS,
                        Namespace symbolNS, IProgramElement programElement,
                        SVInstantiations svInst) throws InstantiationException;

        /**
         * Collects all program variables within the program element.
         * 
         * @param programElement
         * @return
         */
        Set collectVariables(IProgramElement programElement);

        /**
         * Collects introduced program variables visible in the scope within a
         * modality containing given program element.
         * 
         * @param programElement
         * @return
         */
        Set collectIntroducedVariables(IProgramElement programElement);

        /**
         * Replaces variables in the program element with new variables from the
         * map.
         * 
         * @param programElement
         * @param map
         * @return
         */
        IProgramElement replaceVariables(IProgramElement programElement, Map map);
}
