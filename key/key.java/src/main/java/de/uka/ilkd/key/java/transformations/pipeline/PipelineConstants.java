package de.uka.ilkd.key.java.transformations.pipeline;

/**
 * @author Alexander Weigl
 * @version 1 (11/6/21)
 */
public interface PipelineConstants {
    String CONSTRUCTOR_NORMALFORM_IDENTIFIER = "$init";
    String OBJECT_INITIALIZER_IDENTIFIER = "$objectInitializer";
    String IMPLICIT_CLASS_PREPARED = "$classPrepared";
    String IMPLICIT_CLASS_INITIALIZED = "$classInitialized";
    String IMPLICIT_CLASS_INIT_IN_PROGRESS = "$classInitializationInProgress";
    String IMPLICIT_CLASS_ERRONEOUS = "$classErroneous";
    String IMPLICIT_CREATED = "$created";
    String IMPLICIT_INITIALIZED = "$initialized";
    String IMPLICIT_TRANSIENT = "$transient";
    String IMPLICIT_TRANSACTION_UPDATED = "$transactionConditionallyUpdated";
    String IMPLICIT_ENCLOSING_THIS = "$enclosingThis";
    String FINAL_VAR_PREFIX = "_outer_final_";
    String VIRTUAL_METHOD_FOR_PARSING = "$virtual_method_for_parsing";
    String VIRTUAL_CLASS_FOR_PARSING = "$virtual_class_for_parsing";
    String IMPLICIT_OBJECT_PREPARE = "$prepare";
    String IMPLICIT_OBJECT_PREPARE_ENTER = "$prepareEnter";
    String IMPLICIT_INSTANCE_ALLOCATE = "$allocate";
}
