/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.recoderext.KeYCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.java.recoderext.SchemaCrossReferenceServiceConfiguration;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import org.key_project.util.lookup.Lookup;

/**
 * this is a collection of common services to the KeY prover. Services include information on the
 * underlying Java model and a converter to transform Java program elements to logic (where
 * possible) and back.
 */
public class Services implements TermServices {
    /**
     * the proof
     */
    private Proof proof;

    /**
     * proof specific namespaces (functions, predicates, sorts, variables)
     */
    private NamespaceSet namespaces = new NamespaceSet();

    /**
     * used to determine whether an expression is a compile-time constant and if so the type and
     * result of the expression
     */
    private final ConstantExpressionEvaluator cee;

    /**
     * used to convert types, expressions and so on to logic elements (in special into to terms or
     * formulas)
     */
    private TypeConverter typeconverter;

    /**
     * the information object on the Java model
     */
    private final JavaInfo javainfo;

    /**
     * variable namer for inner renaming
     */
    private final VariableNamer innerVarNamer = new InnerVariableNamer(this);

    /**
     * map of names to counters
     */
    private final HashMap<String, Counter> counters;

    /**
     * specification repository
     */
    private SpecificationRepository specRepos;

    /*
     * the Java model (with all paths)
     */
    private JavaModel javaModel;

    private NameRecorder nameRecorder;

    private ITermProgramVariableCollectorFactory factory =
        TermProgramVariableCollector::new;

    private final Profile profile;

    private final ServiceCaches caches;

    private final TermBuilder termBuilder;

    private final TermBuilder termBuilderWithoutCache;

    /**
     * creates a new Services object with a new TypeConverter and a new JavaInfo object with no
     * information stored at none of these.
     */
    public Services(Profile profile) {
        assert profile != null;
        this.profile = profile;
        this.counters = new LinkedHashMap<>();
        this.caches = new ServiceCaches();
        this.termBuilder = new TermBuilder(new TermFactory(caches.getTermFactoryCache()), this);
        this.termBuilderWithoutCache = new TermBuilder(new TermFactory(), this);
        this.specRepos = new SpecificationRepository(this);
        cee = new ConstantExpressionEvaluator(this);
        typeconverter = new TypeConverter(this);
        javainfo = new JavaInfo(
            new KeYProgModelInfo(this, typeconverter, new KeYRecoderExcHandler()), this);
        nameRecorder = new NameRecorder();
    }

    private Services(Profile profile, KeYCrossReferenceServiceConfiguration crsc,
            KeYRecoderMapping rec2key, HashMap<String, Counter> counters, ServiceCaches caches) {
        assert profile != null;
        assert counters != null;
        assert caches != null;

        this.profile = profile;
        this.counters = counters;
        this.caches = caches;
        this.termBuilder = new TermBuilder(new TermFactory(caches.getTermFactoryCache()), this);
        this.termBuilderWithoutCache = new TermBuilder(new TermFactory(), this);
        this.specRepos = new SpecificationRepository(this);
        cee = new ConstantExpressionEvaluator(this);
        typeconverter = new TypeConverter(this);
        javainfo = new JavaInfo(new KeYProgModelInfo(this, crsc, rec2key, typeconverter), this);
        nameRecorder = new NameRecorder();
    }

    private Services(Services s) {
        this.profile = s.profile;
        this.proof = s.proof;
        this.namespaces = s.namespaces;
        this.cee = s.cee;
        this.typeconverter = s.typeconverter;
        this.javainfo = s.javainfo;
        this.counters = s.counters;
        this.specRepos = s.specRepos;
        this.javaModel = s.javaModel;
        this.nameRecorder = s.nameRecorder;
        this.factory = s.factory;
        this.caches = s.caches;
        this.termBuilder = new TermBuilder(new TermFactory(caches.getTermFactoryCache()), this);
        this.termBuilderWithoutCache = new TermBuilder(new TermFactory(), this);
    }

    public Services getOverlay(NamespaceSet namespaces) {
        Services result = new Services(this);
        result.setNamespaces(namespaces);
        return result;
    }


    /**
     * Returns the TypeConverter associated with this Services object.
     */
    public TypeConverter getTypeConverter() {
        return typeconverter;
    }


    private void setTypeConverter(TypeConverter tc) {
        typeconverter = tc;
    }


    /**
     * Returns the ConstantExpressionEvaluator associated with this Services object.
     */
    public ConstantExpressionEvaluator getConstantExpressionEvaluator() {
        return cee;
    }


    /**
     * Returns the JavaInfo associated with this Services object.
     */
    public JavaInfo getJavaInfo() {
        return javainfo;
    }


    public NameRecorder getNameRecorder() {
        return nameRecorder;
    }


    public void saveNameRecorder(Node n) {
        n.setNameRecorder(nameRecorder);
        nameRecorder = new NameRecorder();
    }


    public void addNameProposal(Name proposal) {
        nameRecorder.addProposal(proposal);
    }


    public SpecificationRepository getSpecificationRepository() {
        return specRepos;
    }


    /**
     * Returns the VariableNamer associated with this Services object.
     */
    public VariableNamer getVariableNamer() {
        return innerVarNamer;
    }

    /**
     * creates a new services object containing a copy of the java info of this object and a new
     * TypeConverter (shallow copy) The copy does not belong to a {@link Proof} object and can hence
     * be used for a new proof.
     *
     * @param shareCaches {@code true} The created {@link Services} will use the same
     *        {@link ServiceCaches} like this instance; {@code false} the created {@link Services}
     *        will use a new empty {@link ServiceCaches} instance.
     * @return the copy
     */
    public Services copy(boolean shareCaches) {
        return copy(getProfile(), shareCaches);
    }

    /**
     * Creates a copy of this {@link Services} in which the {@link Profile} is replaced. The copy
     * does not belong to a {@link Proof} object and can hence be used for a new proof.
     *
     * @param profile The new {@link Profile} to use in the copy of this {@link Services}.
     * @param shareCaches {@code true} The created {@link Services} will use the same
     *        {@link ServiceCaches} like this instance; {@code false} the created {@link Services}
     *        will use a new empty {@link ServiceCaches} instance.
     * @return The created copy.
     */
    public Services copy(Profile profile, boolean shareCaches) {
        Debug.assertTrue(
            !(getJavaInfo().getKeYProgModelInfo()
                    .getServConf() instanceof SchemaCrossReferenceServiceConfiguration),
            "services: tried to copy schema cross reference service config.");
        ServiceCaches newCaches = shareCaches ? caches : new ServiceCaches();
        Services s = new Services(profile, getJavaInfo().getKeYProgModelInfo().getServConf(),
            getJavaInfo().getKeYProgModelInfo().rec2key().copy(), copyCounters(), newCaches);
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        s.setJavaModel(getJavaModel());
        return s;
    }

    /**
     * Generate a copy of this object. All references are copied w/o duplicating their content.
     *
     * @return a freshly created Services object
     */
    public Services shallowCopy() {
        return new Services(this);
    }

    /**
     * Creates a deep copy of {@link #counters} which means that a new list is created with a copy
     * of each contained {@link Counter}.
     *
     * @return The created deep copy with new {@link Counter} instances.
     */
    private HashMap<String, Counter> copyCounters() {
        HashMap<String, Counter> result = new LinkedHashMap<>();
        for (Entry<String, Counter> entry : counters.entrySet()) {
            result.put(entry.getKey(), entry.getValue().copy());
        }
        return result;
    }

    /**
     * creates a new service object with the same ldt information as the actual one
     */
    public Services copyPreservesLDTInformation() {
        Debug.assertTrue(
            !(javainfo.getKeYProgModelInfo()
                    .getServConf() instanceof SchemaCrossReferenceServiceConfiguration),
            "services: tried to copy schema cross reference service config.");
        Services s = new Services(getProfile());
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        s.setJavaModel(getJavaModel());

        return s;
    }


    /**
     * Marks this services as proof specific Please make sure that the {@link Services} does not not
     * yet belong to an existing proof or that it is owned by a proof environment. In both cases
     * copy the {@link InitConfig} via {@link InitConfig#deepCopy()} or one of the other copy
     * methods first.
     *
     * @param p_proof the Proof to which this {@link Services} instance belongs
     */
    public void setProof(Proof p_proof) {
        if (this.proof != null) {
            throw new IllegalStateException(
                "Services are already owned by another proof:" + proof.name());
        }
        proof = p_proof;
    }


    public Services copyProofSpecific(Proof p_proof, boolean shareCaches) {
        ServiceCaches newCaches = shareCaches ? caches : new ServiceCaches();
        final Services s =
            new Services(getProfile(), getJavaInfo().getKeYProgModelInfo().getServConf(),
                getJavaInfo().getKeYProgModelInfo().rec2key(), copyCounters(), newCaches);
        s.proof = p_proof;
        s.specRepos = specRepos;
        s.setTypeConverter(getTypeConverter().copy(s));
        s.setNamespaces(namespaces.copy());
        nameRecorder = nameRecorder.copy();
        s.setJavaModel(getJavaModel());

        return s;
    }


    /*
     * returns an existing named counter, creates a new one otherwise
     */
    public Counter getCounter(String name) {
        Counter c = counters.get(name);
        if (c != null) {
            return c;
        }
        c = new Counter(name);
        counters.put(name, c);
        return c;
    }

    /**
     * Reset all counters associated with this service.
     * Only use this method if the proof is empty!
     */
    public void resetCounters() {
        if (proof.root().childrenCount() > 0) {
            throw new IllegalStateException("tried to reset counters on non-empty proof");
        }
        counters.clear();
    }

    /**
     * returns the namespaces for functions, predicates etc.
     *
     * @return the proof specific namespaces
     */
    @Override
    public NamespaceSet getNamespaces() {
        return namespaces;
    }


    /**
     * sets the namespaces of known predicates, functions, variables
     *
     * @param namespaces the NamespaceSet with the proof specific namespaces
     */
    public void setNamespaces(NamespaceSet namespaces) {
        this.namespaces = namespaces;
    }


    /**
     * Returns the proof to which this object belongs, or null if it does not belong to any proof.
     */
    public Proof getProof() {
        return proof;
    }

    public interface ITermProgramVariableCollectorFactory {
        TermProgramVariableCollector create(Services services);
    }

    /**
     * Returns the sued {@link Profile}.
     *
     * @return The used {@link Profile}.
     */
    public Profile getProfile() {
        return profile;
    }

    /**
     * Returns the used {@link ServiceCaches}.
     *
     * @return The used {@link ServiceCaches}.
     */
    public ServiceCaches getCaches() {
        return caches;
    }

    /**
     *
     * Returns either the cache backed or raw {@link TermBuilder} used to create {@link Term}s.
     * Usually the cache backed version is the intended one. The non-cached version is for use cases
     * where a lot of intermediate terms are created of which most exist only for a very short time.
     * To avoid polluting the cache it is then recommended to use the non-cache version
     *
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    @Override
    public TermBuilder getTermBuilder(boolean withCache) {
        return withCache ? termBuilder : termBuilderWithoutCache;
    }

    /**
     * Returns the {@link TermBuilder} used to create {@link Term}s. Same as
     * {@link #getTermBuilder(true).
     *
     * @return The {@link TermBuilder} used to create {@link Term}s.
     */
    @Override
    public TermBuilder getTermBuilder() {
        return termBuilder;
    }

    /**
     * Returns the {@link TermFactory} used to create {@link Term}s.
     *
     * @return The {@link TermFactory} used to create {@link Term}s.
     */
    @Override
    public TermFactory getTermFactory() {
        return termBuilder.tf();
    }

    public ITermProgramVariableCollectorFactory getFactory() {
        return factory;
    }


    public void setFactory(ITermProgramVariableCollectorFactory factory) {
        this.factory = factory;
    }


    /**
     * returns the {@link JavaModel} with all path information
     *
     * @return the {@link JavaModel} on which this services is based on
     */
    public JavaModel getJavaModel() {
        return javaModel;
    }


    public void setJavaModel(JavaModel javaModel) {
        assert this.javaModel == null;
        this.javaModel = javaModel;
    }

    public Lookup createLookup() {
        Lookup lookup = new Lookup();
        lookup.register(getJavaInfo());
        lookup.register(getJavaModel());
        lookup.register(getProfile());
        lookup.register(getProof());
        lookup.register(getNamespaces());
        lookup.register(getTermBuilder());
        lookup.register(getNameRecorder());
        lookup.register(getVariableNamer());
        return lookup;
    }
}
