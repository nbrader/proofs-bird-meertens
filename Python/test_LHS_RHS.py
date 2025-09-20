import random

def nonNegPlus(v, x):
    """Coq's nonNegPlus: v + x but truncated to be >= 0"""
    return max(0, v + x)

def scan_left(f, xs, init):
    """Left scan: like Coq's scan_left"""
    acc = init
    result = []
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def fold_left(f, xs, init):
    """Left fold"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def LHS(ys, u_acc, v_acc):
    acc = (u_acc, v_acc)
    for x in ys:
        u, v = acc
        v_new = nonNegPlus(v, x)
        u_new = max(u, v_new)
        acc = (u_new, v_new)
    return acc

def RHS(ys, u_acc, v_acc):
    first = fold_left(max, scan_left(nonNegPlus, ys, v_acc), u_acc)
    second = fold_left(nonNegPlus, ys, v_acc)
    return (first, second)

def test_one(ys, u_acc, v_acc):
    if v_acc < 0 or u_acc < v_acc:
        return True  # only test under hypotheses
    return LHS(ys, u_acc, v_acc) == RHS(ys, u_acc, v_acc)

# Run many random tests
ok = True
for _ in range(10000):
    ys = [random.randint(-5, 10) for _ in range(random.randint(0,5))]
    u_acc = random.randint(-5, 20)
    v_acc = random.randint(0, 20)  # ensures v_acc >= 0
    if u_acc < v_acc:
        continue
    if not test_one(ys, u_acc, v_acc):
        print("Counterexample found:")
        print(f"ys={ys}, u_acc={u_acc}, v_acc={v_acc}")
        print("LHS:", LHS(ys, u_acc, v_acc))
        print("RHS:", RHS(ys, u_acc, v_acc))
        ok = False
        break

if ok:
    print("Property held for all tested cases")
