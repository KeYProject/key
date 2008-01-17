package de.uka.ilkd.key.lang.clang.safe.services;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.lang.clang.common.iface.IClangEnvironment;
import de.uka.ilkd.key.lang.clang.common.iface.IClangServices;
import de.uka.ilkd.key.lang.clang.common.loader.ConversionException;
import de.uka.ilkd.key.lang.clang.common.loader.ILoaderConfiguration;
import de.uka.ilkd.key.lang.clang.common.loader.Loader;
import de.uka.ilkd.key.lang.clang.common.program.expression.literal.IntegerLiteral;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberReference;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ValueOf;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.statement.ContextFrame;
import de.uka.ilkd.key.lang.clang.common.program.type.TypeReference;
import de.uka.ilkd.key.lang.clang.common.program.variable.Variable;
import de.uka.ilkd.key.lang.clang.common.programmeta.IClangProgramMeta;
import de.uka.ilkd.key.lang.clang.common.programmeta.ProgamMetaBuilder;
import de.uka.ilkd.key.lang.clang.common.programsv.ProgramSVSortBuilder;
import de.uka.ilkd.key.lang.clang.common.sort.object.MemberInfo;
import de.uka.ilkd.key.lang.clang.common.type.IntegerTypeUtil;
import de.uka.ilkd.key.lang.clang.common.type.TypeBuilder;
import de.uka.ilkd.key.lang.clang.common.walker.IntroducedVariableCollector;
import de.uka.ilkd.key.lang.clang.common.walker.ProgramInstantiator;
import de.uka.ilkd.key.lang.clang.common.walker.VariableCollector;
import de.uka.ilkd.key.lang.clang.common.walker.VariableReplacer;
import de.uka.ilkd.key.lang.clang.safe.metaop.MetaOpBuilder;
import de.uka.ilkd.key.lang.clang.safe.sort.IntegerSortUtil;
import de.uka.ilkd.key.lang.clang.safe.sort.SortBuilder;
import de.uka.ilkd.key.lang.clang.safe.sort.object.ScalarSort;
import de.uka.ilkd.key.lang.clang.safe.sort.object.StructSort;
import de.uka.ilkd.key.lang.clang.safe.sort.value.IntegerSort;
import de.uka.ilkd.key.lang.common.metaop.BaseMetaOp;
import de.uka.ilkd.key.lang.common.metaop.MetaOpProgramElementSymbol;
import de.uka.ilkd.key.lang.common.program.BaseVariable;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.program.IVariable;
import de.uka.ilkd.key.lang.common.programsv.ArrayOfBaseProgramSV;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSVSort;
import de.uka.ilkd.key.lang.common.programsv.IVariableProgramSVSort;
import de.uka.ilkd.key.lang.common.services.ILangServices;
import de.uka.ilkd.key.lang.common.services.ILangServicesEnv;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Safe CDL language services.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ClangSafeServices implements IClangServices {
        private final ILangServicesEnv langServicesEnv;

        private final TypeBuilder typeBuilder;

        private final Map programSVSortMap;

        private final Map metaOpMap;

        private final Map programMetaMap;

        /**
         * A map from integer type IDs to corresponding integer sorts.
         */
        private final Map integerTypeIdSortMap;

        private SortBuilder getSortBuilder(Namespace sortNS,
                        Namespace symbolNS) {
                return new SortBuilder(langServicesEnv.getSymbolEnv(sortNS, symbolNS));
        }

        public ClangSafeServices(ILangServicesEnv environment) {
                this.langServicesEnv = environment;
                this.typeBuilder = new TypeBuilder();
                IntegerTypeUtil.registerStandardTypeDecls(typeBuilder);
                this.programSVSortMap = ProgramSVSortBuilder.buildMap();
                this.metaOpMap = MetaOpBuilder.buildMap();
                this.programMetaMap = ProgamMetaBuilder.buildMap();
                this.integerTypeIdSortMap = new HashMap();
        }

        /**
         * Internal constructor for shallow copying.
         * 
         * @param environment
         * @param typeBuilder
         * @param programSVSortMap
         * @param metaOpMap
         */
        private ClangSafeServices(ILangServicesEnv environment,
                        TypeBuilder typeBuilder, Map programSVSortMap,
                        Map metaOpMap, Map programMetaMap, Map integerTypeIdSortMap) {
                this.langServicesEnv = environment;
                this.typeBuilder = typeBuilder;
                this.programSVSortMap = programSVSortMap;
                this.metaOpMap = metaOpMap;
                this.programMetaMap = programMetaMap;
                this.integerTypeIdSortMap = integerTypeIdSortMap;
        }

        /**
         * @inheritDoc
         */
        public ILangServices copy(ILangServicesEnv environment) {
                return new ClangSafeServices(environment, typeBuilder.copy(),
                                programSVSortMap, metaOpMap, programMetaMap, integerTypeIdSortMap);
        }

        /**
         * @inheritDoc
         */
        public ILangServices newInstance(ILangServicesEnv environment) {
                return new ClangSafeServices(environment);
        }

        /**
         * @inheritDoc
         */
        public void init(Namespace sortNS, Namespace symbolNS) {
                SortBuilder sortBuilder = getSortBuilder(sortNS, symbolNS);
                sortBuilder.init();
                IntegerSortUtil.registerStandardSorts(sortBuilder,
                                integerTypeIdSortMap);
        }

        /**
         * @inheritDocs
         */
        public void lazyBuildSort(Namespace sortNS, Namespace symbolNS, Name sortName) {
                // TODO: scalar and array sorts must be created on demand
        }

        /**
         * @inheritDocs
         */
        public void lazyBuildSymbol(Namespace sortNS, Namespace symbolNS, Name symbolName) {
                String str = symbolName.toString();
                int index = str.indexOf("::");
                if (index == -1)
                        return;
                else
                        lazyBuildSort(sortNS, symbolNS, new Name(str.substring(index + 2)));
        }

        /**
         * @inheritDocs
         */
        public void loadProgram(Namespace sortNS, Namespace symbolNS,
                        String path) throws IOException, ConvertException {
                try {
                        Loader.loadProgram(getLoaderConfiguration(sortNS,
                                        symbolNS), new String[] { path });
                } catch (ConversionException e) {
                        throw new ConvertException(e);
                }
        }

        /**
         * @inheritDocs
         */
        public IProgramElement loadStatements(Namespace sortNS,
                        Namespace symbolNS, Namespace schemaVariableNS,
                        Namespace programVariableNS, String code) throws ConvertException{
                try {
                        return Loader.loadProgramStatements(getLoaderConfiguration(
                                        sortNS, symbolNS), schemaVariableNS,
                                        programVariableNS, code);
                } catch (ConversionException e) {
                        throw new ConvertException(e);
                }
        }

        /**
         * @inheritDocs
         */
        public Term convertProgramElementToTerm(Namespace sortNS,
                        Namespace symbolNS, IProgramElement programElement) {
                if (programElement instanceof ProgramVariable)
                        return TermFactory.DEFAULT
                                        .createVariableTerm((ProgramVariable) programElement);
                if (programElement instanceof MemberReference)
                        return TermFactory.DEFAULT
                                        .createFunctionTerm(new MetaOpProgramElementSymbol(programElement));
                else if (programElement instanceof ValueOf) {
                        ValueOf valueOf = (ValueOf) programElement;
                        IClangExpression expression = valueOf.getExpressionAt(0);
                        if (expression instanceof ProgramVariable) {
                                return TermFactory.DEFAULT
                                                .createFunctionTerm(
                                                                ((ScalarSort) ((IProgramVariable) expression)
                                                                                .getKeYJavaType()
                                                                                .getSort())
                                                                                .getValueLocation(),
                                                                TermFactory.DEFAULT
                                                                                .createVariableTerm((ProgramVariable) expression));
                        }
                } else if (programElement instanceof IntegerLiteral) {
                        Term value = langServicesEnv.getSymbolEnv(sortNS, symbolNS).encodeInteger(
                                        ((IntegerLiteral) programElement)
                                                        .getValue());
                        IntegerSort integerSort = ((IntegerSort) ((IntegerLiteral) programElement)
                                        .getType().getSort());
                        return TermFactory.DEFAULT
                                        .createFunctionTerm(integerSort
                                                        .getFromIntFunction(),
                                                        value);
                } else if (programElement instanceof TypeReference) {
                        TypeReference typeRef = (TypeReference) programElement;
                        Sort sort = typeRef.getTypePair().getSort();
                        if (sort instanceof AbstractSort)
                                return TermFactory.DEFAULT
                                                .createCastTerm(
                                                                (AbstractSort) sort,
                                                                TermFactory.DEFAULT
                                                                                .createFunctionTerm(langServicesEnv
                                                                                                .getSymbolEnv(sortNS, symbolNS)
                                                                                                .getNullConstant()));
                }

                return null;
        }
        
        /**
         * @inheritDocs
         */
        public BaseVariable buildVariable(IVariableProgramSVSort programSVSort, Name name, KeYJavaType typePair) {
                return new Variable(name, typePair);
        }
        
        /**
         * @inheritDocs
         */
        public BaseVariable copyVariable(IVariable prototypeVariable, Name name, KeYJavaType typePair) {
                return new Variable(name, typePair);
        }
        
        /**
         * @inheritDocs
         */
        public String getVariableNameProposal(KeYJavaType typePair) {
                return typePair.getJavaType().getName().toString().replaceAll(
                                "struct ", "struct_").replaceAll("@", "_obj")
                                .replaceAll("\\*", "_ptr").replaceAll("\\[",
                                                "_arr").replaceAll("\\]", "")
                                .replaceAll("[^a-zA-Z0-9_]", "_");
        }

        /**
         * @inheritDocs
         */
        public BaseProgramSVSort getProgramSVSort(Name name) {
                return (BaseProgramSVSort) programSVSortMap.get(name);
        }

        /**
         * @inheritDocs
         */
        public BaseMetaOp getMetaOp(Name name) {
                return (BaseMetaOp) metaOpMap.get(name);
        }

        /**
         * @inheritDocs
         */
        public IProgramElement instantiateProgram(
                        Namespace sortNS, Namespace symbolNS,
                        IProgramElement programElement, SVInstantiations svInst) {
                ProgramInstantiator instantiator = new ProgramInstantiator(programElement, getEnvironment(sortNS, symbolNS), svInst);
                instantiator.start();
                programElement = instantiator.result();
                
                if (programElement instanceof ContextFrame) {
                        ContextFrame contextFrame = (ContextFrame) programElement;

                        ContextFrame.ContextInstantiation inst = (ContextFrame.ContextInstantiation) svInst
                                        .getInstantiation(ContextFrame.CONTEXTSV);
                        if (inst == null)
                                throw new IllegalStateException(
                                                "Context should also be instantiated");

                        return contextFrame.instantiate(inst);

                } else
                        return programElement;
        }

        public Set collectIntroducedVariables(IProgramElement programElement) {
                IntroducedVariableCollector collector = new IntroducedVariableCollector(
                                programElement);
                collector.start();
                return collector.result();
        }
        
        public Set collectVariables(IProgramElement programElement) {
                VariableCollector collector = new VariableCollector(
                                programElement);
                collector.start();
                return collector.result();                
        }
        
        public IProgramElement replaceVariables(IProgramElement programElement,
                        Map map) {
                VariableReplacer replacer = new VariableReplacer(programElement, map);
                replacer.start();
                return replacer.result();
        }
        
        private ILoaderConfiguration getLoaderConfiguration(Namespace sortNS,
                        Namespace symbolNS) {
                final SortBuilder sortBuilder = getSortBuilder(sortNS,
                                symbolNS);
                final IClangEnvironment environment = getEnvironment(sortNS,
                                symbolNS);
                return new ILoaderConfiguration() {
                        public IClangEnvironment getEnvironment() {
                                return environment;
                        }

                        public TypeBuilder getTypeBuilder() {
                                return typeBuilder;
                        }

                        public StructSortInfo getStructSortInfo(final String id) {
                                StructSort existingStructSort = sortBuilder
                                                .getStructSort(id);
                                final StructSort structSort = existingStructSort != null ? existingStructSort
                                                : sortBuilder
                                                                .preregisterStructSort(id);
                                return new StructSortInfo() {
                                        public boolean wasRegistered() {
                                                return structSort
                                                                .getWasRegistered();
                                        }

                                        public void addMember(MemberInfo info) {
                                                structSort
                                                                .getMemberInfoMap()
                                                                .put(
                                                                                info
                                                                                                .getId(),
                                                                                info);
                                        }

                                        public void register() {
                                                sortBuilder
                                                                .registerStructSort(id);

                                        }
                                };
                        }

                        public IClangProgramMeta getProgramMetaConstruct(
                                        Name name, ArrayOfBaseProgramSV arguments) {
                                Class clazz = (Class) programMetaMap.get(name);

                                if (clazz == null)
                                        return null;

                                Object metaConstruct;
                                try {
                                        metaConstruct = clazz
                                                        .getConstructor(
                                                                        new Class[] { ArrayOfBaseProgramSV.class })
                                                        .newInstance(
                                                                        new Object[] { arguments });
                                } catch (Exception e) {
                                        throw new RuntimeException(e);
                                }
                                return (IClangProgramMeta) metaConstruct;

                        }

                };

        }

        /**
         * Creates the environment associated with this instance.
         * 
         * @return
         */
        public IClangEnvironment getEnvironment(final Namespace sortNS,
                        final Namespace symbolNS) {
                return new ClangSafeEnvironment(langServicesEnv, sortNS, symbolNS,
                                new ClangSafePlatform(typeBuilder, getSortBuilder(
                                                sortNS, symbolNS),
                                                integerTypeIdSortMap));
        }
}
