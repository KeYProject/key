/**
 * The (new) list system for recoder. as of now, the regular java.util.List is used for
 * non-AST-Lists. It replaces the old XYZList<br>
 * ASTList reflects a (mutable!) list which reflects that changes applied to it have effect on the
 * AST structure. It replaces the old ProgramElementList interface. It further defines a deepClone()
 * method. ASTArrayList is currently the only implementor.
 */
package recoder.list.generic;
