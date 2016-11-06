class Entity:
	def __repr__(self):
		return str(self)
	def __eq__(self, other):
		return self.__dict__ == other.__dict__
	def __hash__(self):
		return hash(frozenset(self.__dict__.items()))

class Type(Entity):
	pass

class BaseType(Type):
	def __init__(self, name):
		assert isinstance(name, str)
		self.name = name
	def __str__(self):
		return self.name

class FunctionType(Type):
	def __init__(self, argument, result):
		assert isinstance(argument, Type)
		assert isinstance(result, Type)
		self.argument = argument
		self.result = result
	def __str__(self):
		return '({} → {})'.format(self.argument, self.result)

class Term(Entity):
	pass

class Constant(Term):
	def __init__(self, name):
		assert isinstance(name, str)
		self.name = name
	def __str__(self):
		return self.name

class Application(Term):
	def __init__(self, function, argument):
		assert isinstance(function, Term)
		assert isinstance(argument, Term)
		self.function = function
		self.argument = argument
	def __str__(self):
		return '({} {})'.format(self.function, self.argument)

class Abstraction(Term):
	def __init__(self, type, body):
		assert isinstance(type, Type)
		assert isinstance(body, Term)
		self.type = type
		self.body = body
	def __str__(self):
		return '(λ:{} {})'.format(self.type, self.body)

class Variable(Term):
	def __init__(self, index):
		assert isinstance(index, int) and index >= 0
		self.index = index
	def __str__(self):
		return '{}'.format(self.index)

def get_size(term):
	'''Returns the number of abstractions and applications in a term'''
	assert isinstance(term, Term)
	if isinstance(term, Constant):
		return 0
	elif isinstance(term, Variable):
		return 0
	elif isinstance(term, Application):
		return 1 + get_size(term.function) + get_size(term.argument)
	elif isinstance(term, Abstraction):
		return 1 + get_size(term.body)

class Context(Entity, dict):
	def __init__(self, dictionary=dict()):
		assert isinstance(dictionary, dict)
		super().__init__()
		for term in dictionary:
			self[term] = dictionary[term]
	def __str__(self):
		return '\n'.join('{} : {}'.format(key, self[key]) for key in sorted(self, key=get_size))
	def __setitem__(self, key, value):
		super().__setitem__(key, value)
		assert isinstance(key, Term)
		assert isinstance(value, Type)
		self.__dict__[key] = value














