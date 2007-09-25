package de.uka.ilkd.asmkey.parser.ast;

import de.uka.ilkd.key.parser.Location;

/**
 * The instances of the class represent a sort that
 * express a universe of an ASM. it consists
 * of an identifier referering to declared sort. it may 
 * be a list of this sort.
 */
public class AstType extends AstNode {

    /* the base sort */
    private Identifier sort;

    /* is it a list or not */
    private boolean is_list;

    AstType(Location location) {
	this(location, new Identifier(location, "") , false);
    }

    AstType(Location location, Identifier sort, boolean is_list) {
	super(location);
	this.sort = sort;
	this.is_list = is_list;
    }

    public Identifier getSort() {
	return sort;
    }

    public boolean isList() {
	return is_list;
    }

    public String getText() {
	String m = "";
	if (isList()) { m = "["; }
	m += getSort().getText();
	if (isList()) { m+= "]"; }
	return m;
    }

    /** for debug only */
    public String toString() {
	return "[AstType:sort=" + sort + ",is_list=" + is_list + "]";
    }

    public static AstType createAsmRuleTypeRef(Location location) {
	return new AstType(location, new Identifier(location, "asm rule"), false);
    }

}
