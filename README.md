# Fiddle-String Snake
![fiddle string snake](./snake.jpg)

## String type:

### Semantics
We added a string expression type

type 'a expr =
  ...
| EString of string * 'a

and complex type since strings need to be stored on the heap
and type 'a cexpr =
  ...
| CString of string * 'a

### Memory layout and tagging

To accommodate them we first edited the tags to now use all four of the lsb.
Now all the masks that used to be 0x7 are 0xF.
This allowed us to us to use 0x7 as our string type tag.

Strings are stored on the heap similarly to tuples.
The first word stores the length of the string as a snakeval.
We then use 16 bits for each character in the string, where the ascii code is stored in the
higher 8 bits and the symbol '@' is stored in the lower 8.
This allows us to avoid mistaking the characters on the heap for pointers when garbage collecting
at the cost of doubling our in memory string size.

### Runtime

We added to printHelp a case for strings which loops over the length of the string and prints
every other character.

## TODO: 
- garbage collection
- concat
- substring
- printf
- sprintf

printf("%d", int) -> soi(int) 
printf("my number: %d", int) -> "my number: " ^ soi(int)

let str = "my number: %d"
printf(str, int) -> "my number: " ^ soi(int)
