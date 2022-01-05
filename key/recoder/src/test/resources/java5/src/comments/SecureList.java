/*
 * Comment1 belongs to CompilationUnit
 */

// Comment2 belongs to CompilationUnit TODO PackageSpecification for now

// Comment3 belongs to PackageSpecification
/* Comment4 belongs to PackageSpecification */
package/*Comment5 belongs to PackageReference*/ /*Comment6 belongs to PackageReference*/ /*Comment7 belongs to PackageReference*/comment/*Comment8 belongs to PackageReference*/;//Comment9 belongs to PackageSpecification
/*
 * Comment10 belongs to PackageSpecification
 */ // Comment11 belongs to PackageSpecification

// Comment12 belongs to Import

// Comment13 belongs to Import
/* Comment14 belongs to Import*/
import /*Comment15 belongs to TypeReference*/ /*Comment16 belongs to PackageReference*/java.util.ArrayList/*Comment17 belongs to TypeReference*/;//Comment18 belongs to Import
import java.util.Hashtable;

/*
 * Comment19 belongs to ClassDeclaration
 */

/**
 * Comment20 belogs to ClassDeclaration
 */
// Comment21 belongs to ClassDeclaration
/*Comment 22 belongs to ClassDeclaration*/ /*Comment23 belongs to Public TODO think again (ClassDeclaration for now)... (compare policy to References, we don't annotate Identifiers there either)*/
public/*Comment24 belongs to Public*/ /*Comment25 belongs to ClassDeclaration*/ /*Comment26 belongs to ClassDeclaration TODO quite impossible => Identifier (which is totally wrong - but where put it ?)*/class /*Comment27 belongs to Identifier*/SecureList<Elem> /*Comment28 belongs to ??? */{

	public static enum Rights {
		ADD,
		GET,
		REMOVE,
		ACLREAD,
		ACLWRITE
	}

	//Comment29 belongs to EnumDeclaration

	//Comment30 belongs to noCaller FieldDeclaration (not field specification)
	private static final /*Comment31 belongs to TypeReference */ String /*Comment32 belongs to FieldSpecification*/noCaller/*Comment33 belongs to FieldSpecification TODO impossible => Identifier*/   /*Comment34 belongs to FieldSpecification TODO impossible => StringLiteral (not that good...)*/    = "<no caller class>"/* Comment35 belongs to FieldSpecification?*/ /*Comment36 belongs to FieldDeclaration*/; //Comment37 belongs to noCaller FieldDeclaration

	//Comment38 belongs to list FieldDeclaration
	private ArrayList<Elem> list;
	//Comment39 belongs to list FieldDeclaration
	private Hashtable<String, Rights[]> rights;
	/*
	 * Comment40 belongs to ConstructorDeclaration
	 */
	public SecureList() /*Comment 41 belongs to StatementBlock*/{
		list = new ArrayList<Elem>();
		//Comment42 belongs to the above statement (CopyAssignment)
		rights = new Hashtable<String, Rights[]>();
		/*
		 * Comment43 belongs to the statement below (MethodReference)
		 */
		rights.put(noCaller, new Rights[] {});
		StackTraceElement[] stelems = Thread.currentThread().getStackTrace();
		if (stelems.length > 3)
			rights.put(stelems[3].getClassName(), new Rights[] {Rights.ADD, Rights.GET, Rights.REMOVE, Rights.ACLREAD, Rights.ACLWRITE});
	}

	/*
	 * Comment44 belongs to MethodDeclaration
	 */

	private String getCallerClass() {
		StackTraceElement[] stelems = Thread.currentThread().getStackTrace();
		if (stelems.length > 5)
			return stelems[5].getClassName();
		return noCaller;
	}
	/**
	 * Comment45 belongs to callerHasRight MethodDeclaration
	 * @param cr
	 * @return
	 */
	/*Comment46 belongs to MethodDeclaration*/ /*Comment47 belongs to Private TODO why not MethodDeclaration*/private boolean callerHasRight(Rights cr) {
		Rights[] tmpRights = rights.get(getCallerClass());
		if (tmpRights != null) {
			for (Rights r : tmpRights)
				if (r == cr)
					return true;
		}
		return false;
	}

	public void setRights(String className, Rights[] crights) throws InsufficientRightsException {
		if (callerHasRight(Rights.ACLWRITE)) {
			rights.put(className, crights);
		}
		else
			throw new InsufficientRightsException();
	}

	public Rights[] getRights(String className) throws InsufficientRightsException {
		if (callerHasRight(Rights.ACLREAD)) {
			Rights[] tmp = rights.get(className);
			if (tmp != null)
				return tmp.clone();
			else
				return null;
		}
		else
			throw new InsufficientRightsException();
	}

	public void add(Elem e) throws InsufficientRightsException {
		if (callerHasRight(Rights.ADD)) {
			list.add(e);
		}
		else
			throw new InsufficientRightsException();
	}

	public void remove(Object e) throws InsufficientRightsException {
		if (callerHasRight(Rights.REMOVE)) {
			list.remove(e);
		}
		else
			throw new InsufficientRightsException();
	}

	public Elem get(int idx) throws InsufficientRightsException {
		if (callerHasRight(Rights.GET)) {
			return list.get(idx);
		}
		else
			throw new InsufficientRightsException();
	}

	public int size() throws InsufficientRightsException {
		if (callerHasRight(Rights.GET)) {
			return list.size();
		}
		else
			throw new InsufficientRightsException();
	}

	public static void main(String[] args) {
		try {
			SecureList<Integer> slist = new SecureList<Integer>();
			slist.add(new Integer(10));
			slist.add(new Integer(20));
			slist.setRights(Client.class.getName(), new Rights[] {Rights.GET});
			new Client().access(slist);
		} catch (InsufficientRightsException e) {
			e.printStackTrace();
		}
	}
}
