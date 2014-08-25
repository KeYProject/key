interface I1{}
interface I2{}
interface I3 extends I1{}
interface I4 extends I1, I2{}
abstract class A implements I4{}
class C1 implements I3{}
class C2 extends A {}
final class C3 extends A {}
class C4 extends C2{}

public class Test{} 
