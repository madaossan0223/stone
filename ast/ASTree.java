package stone.ast;

import java.util.Iterator;

/*
 *               +------------+
 *               |   ASTree   |
 *               |------------| <-------------------+
 *               |child(int)  |                     |
 *               |children()  |                     |
 *               +------------+                     |
 *                     ^                            |
 *                     |                            |
 *             +-----------------------+            |
 *             |                       |            |
 *          ASTLeaf                  ASTList  <>----+
 *             ^                       ^
 *             |                       |
 *         +---+--------+              |
 *         |            |              |
 *    NumberLiteral    Name         BinaryExpr
 *
 */

public abstract class ASTree implements Iterable<ASTree> {
    public abstract ASTree child(int i);
    public abstract int numChildren();
    public abstract Iterator<ASTree> children();
    public abstract String location();
    public Iterator<ASTree> iterator() { return children(); }
}