# A second world, about who studies and teaches what.  
# Quantification here ranges over two sorts of individual, people and courses.

students = ['Ana', 'Boris', 'Chen', 'Elena']
teachers = ['Mira', 'Nadia']
courses  = ['algebra', 'logic', 'topology']

people = students + teachers
things = people + courses

takes   = { ('Ana','logic'), ('Ana','algebra'), ('Boris','algebra'),
            ('Chen','topology'), ('Elena','logic'), ('Elena','topology') }
teaches = { ('Mira','logic'), ('Mira','topology'), ('Nadia','algebra') }

passes = { 'Ana', 'Chen', 'Elena' }

hard = { 'logic', 'topology' }
easy = { 'algebra' }
