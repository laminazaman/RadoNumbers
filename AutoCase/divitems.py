class DivItem:
    def __init__(self, exp, divides):
        self.exp = exp
        self.divides = divides
    
    def get(self):
        return (self.exp, self.divides)

class DivItems:
    def __init__(self, divitems=None):
        self.divitems = list()
        if divitems != None:
            for item in divitems:
                self.divitems.append(DivItem(item[0], item[1]))
    
    def add(self, divitem):
        self.divitems.append(DivItem(divitem[0], divitem[1]))

    def get(self):
        return [item.get() for item in self.divitems]
