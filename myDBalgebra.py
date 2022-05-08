from dataclasses import dataclass
from myDBtables import * 
@dataclass
class Table:
    name: object #name of the table
    data: object #contents of the table


@dataclass
class Value:
    pass


@dataclass
class Attribute(Value):
    tab: object #name of the table
    name: object #name of the attribute


@dataclass
class Constant(Value):
    c: object


@dataclass
class Func:
    symb: object #symbol for printing
    f: object #function itself


@dataclass
class Test:
    func: Func #binary function of the test
    op1: Value #first operand, attribute or constant
    op2: Value #first operand, attribute or constant


@dataclass
class UnOp:
    mid: object #child of the unry operator


@dataclass
class Project(UnOp):
    symb = "Project"
    list: object #list of attributes we want to project on


@dataclass
class Restrict(UnOp):
    symb = "Restrict"
    test: object #test we want to restrict on


@dataclass
class BinOp:
    left: object #left child of the unry operator
    right: object #right child of the unry operator


class Times(BinOp):
    symb = "Times"

class Join(BinOp):
    symb = "Join"


###Tree functions###


# copy_tree makes a copy of the tree t.
# like in lists, writing s=t then modifying s would modify t
# when you want to give to a variable the same value as t, use copy_tree(t)
def copy_tree(t):
    match t:
        case Table(name, data):
            return Table(name, data)
        case Constant(c):
            return Constant(c)
        case Attribute(name, att):
            return Attribute(name, att)
        case Func(symb, f):
            return Func(symb, f)
        case Test(f, op1, op2):
            return Test(copy_tree(f), copy_tree(op1), copy_tree(op2))
        case Restrict(mid,test):
            return Restrict(copy_tree(mid),copy_tree(test))
        case Project(mid,l):
            return Project(copy_tree(mid),l.copy())
        case Times(left, right):
            return Times(copy_tree(left),copy_tree(right))
        case Join(left, right):
            return Join(copy_tree(left), copy_tree(right))
        case _:
            return "XXX"


# string_tree generates a well-bracketed expression corresponding to a tree
def string_tree(t):
    match t:
        # To print a table: index:name
        case Table(name, d):
            return f"{name}"
        # To print a constant, print its value
        case Constant(c=val):
            return f"{val}"
        # To print an attribute: index.name, with the table's index
        case Attribute(tab, name):
            return f"{tab}.{name}"
        # To print a function: print its symbol
        case Func(symb):
            return f"{symb}"
        # To print a test: f(op1,op2)
        #   f the binary test function
        #   op1 the test's first operand
        #   op2 the test's second operand
        case Test(f, op1, op2):
            return f"{string_tree(f)}({string_tree(op1)},{string_tree(op2)})"
        # To print a restriction: Restr[test](child)
        case Restrict(mid, test):
            return f"{t.symb}[{string_tree(test)}]({string_tree(mid)})"
        # To print a list (that we assume to be a list of attributes for Project, for instance)
        # Print every attribute, separated by ", "
        case list():
            res = map(string_tree, iter(t))
            return ", ".join(res)
        # To print a projection: Restr[list of attributes](child)
        case Project(mid, l):
            return f"{t.symb}[{string_tree(l)}]({string_tree(mid)})"
        # To print a product: Times(left,right)
        #   childL and childR are the left and right children of the node
        case Times(l,r):
            return f"{t.symb}({string_tree(l)},{string_tree(r)})"
        case Join(l,r):
            return f"{t.symb}({string_tree(l)},{string_tree(r)})"
        case _:
            return "XXX"


def implem_tree(t):
    match t:
        case Table(name, data):
            return data
        case Project(mid, l):
            match mid:
                case Times(left, right):
                    newLeft = prefixed_table(left.data, left.name)
                    newRight = prefixed_table(right.data, right.name)
                    timesTable = product_table(newLeft, newRight)
                    result = project_table(timesTable, l)
                    return result
                case _:
                    newMid = implem_tree(mid)
                    result = project_table(newMid, l)
                    return result
        case Restrict(mid, test):
            match mid:
                case Times(left, right):
                    newLeft = prefixed_table(left.data, left.name)
                    newRight = prefixed_table(right.data, right.name)
                    timesTable = product_table(newLeft, newRight)
                    result = restrict_table(timesTable, test)
                    if (string_tree(test.op2) in result):
                        result.pop(string_tree(test.op2))
                    return result
                case _:
                    newMid = implem_tree(mid)
                    result = restrict_table(newMid, test)
                    return result

        case Times(left, right):
            return product_table(left, right)
        case Join(joinLeft, joinRight, joinOp1, joinOp2):
            def eq(a, b):
                return a == b
            if (type(joinLeft) is Restrict):
                joinLeft = implem_tree(joinLeft)
            if (type(joinRight) is Restrict):
                joinRight = implem_tree(joinRight)

            funceq = Func(symb="Equal", f=eq)
            testJoin = Test(func=funceq, op1=joinOp1, op2=joinOp2)

            timesTable = product_table(joinLeft, joinRight)
            result = restrict_table(timesTable, testJoin)
            if (string_tree(testJoin.op2) in result):
                result.pop(string_tree(testJoin.op2))
            return result

def is_in(t, s):
    return s in string_tree(t)

def on_table(v):
    match v:
        case Attribute(tab, name):
            return tab
        case Constant(c):
            return None

def insert_restrict(t,tst):
    """We use recursive with match case to traverse through our tree.
       If table of op2 is None then mid is a table, otherwise it is a result of a Times.
       So we stop the recursive upon reaching the destination table and insert a Restrict"""

    if on_table(tst.op2) is None: 
        match t:
            case Table(name, data):
                if name == on_table(tst.op1):
                    return Restrict(test=tst, mid=copy_tree(t))
                else:
                    return None
            case Restrict(mid, test):
                return Restrict(insert_restrict(mid,tst), test)
            case Project(mid, l):
                return Project(insert_restrict(mid,tst), l.copy())
            case Times(left, right):
                if is_in(left,on_table(tst.op1)):
                    return Join(insert_restrict(left, tst),copy_tree(right))
                else:
                    return Join(copy_tree(left), insert_restrict(right, tst))
            case _:
                return t
    else:
        match t:
            case Table(name, data):
                if name == on_table(tst.op1):
                    return Restrict(test=tst, mid=t)
                else:
                    return None
            case Restrict(mid, test):
                if is_in(mid,tst.op1):
                    if is_in(mid, tst.op2):
                        return Restrict(insert_restrict(mid, tst), test)
                else:
                    return Restrict(test=tst, mid=t)
            case Project(mid, l):
                if is_in(mid,tst.op1):
                    if is_in(mid, tst.op2):
                        return Project(insert_restrict(mid, tst), l.copy())
                else:
                    return Project(Restrict(test = tst,mid=t), l.copy())
            case Times(left, right):
                if is_in(left,tst.op1) and is_in(left, tst.op2) :
                    return implem_join(tst,insert_restrict(left, tst), right)
                elif is_in(right,tst.op1) and is_in(right, tst.op2):
                    return implem_join(tst, left, insert_restrict(right, tst))
                else:
                    return Restrict(test= tst, mid=t)
            case _:
                return t
def make_query_tree(lS, lF, lW):
    '''
    if on_table(lW[0].op2) is not None:
        temp = Restrict(
            test= lW[0],
            mid=Times(
                left = lF[0],
                right = lF[1]
            )
        )
    else:
        temp = Restrict(
            test= lW[0],
            mid= lF[0]
        )
    '''
    temp = Restrict(
        mid = Times(
            left = lF[0],
            right = lF[1]
        ),
        test = lW[0]
    )
    for i in range(1,len(lW)):
        temp = insert_restrict(temp,lW[i])

    return Project(mid=copy_tree(temp) , list= lS)

# def implem_join(test,left,right):
#     return Restrict(Times(left=left, right=right), test)




