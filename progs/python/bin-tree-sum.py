class BinTree:
    def __init__(self, value, left=None, right=None):
        self.value = value
        self.left = left
        self.right = right

    def values(self):
        if self.left is not None:
            yield from self.left.values()
        yield self.value
        if self.right is not None:
            yield from self.right.values()


tree = BinTree(11,
            BinTree(7,
                    BinTree(3),
                    BinTree(9)),
            BinTree(15,
                    BinTree(13),
                    BinTree(19,
                            BinTree(18))))
for v in tree.values():
    print(v)



