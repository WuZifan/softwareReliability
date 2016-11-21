// RUN: %tool "%s" > "%t"
// RUN: %diff %CORRECT "%t"
int main(int i,int j,int z) {
<<<<<<< HEAD
int a;
int b;
int c;
int d;
a=0; 
b=0;
c=0;
d=0;
if(i) {
if(j) {
a=1;
} else {
b=1;
}
} else {
if(z) {
c=1;
} else {
d=1;
}
}
assert(!(i&&j)||(a&&!b&&!c&&!d));
assert(!(i&&!j)||(!a&&b&&!c&&!d));
assert(!(!i&&z)||(!a&&!b&&c&&!d));
assert(!(!i&&!z)||(!a&&!b&&!c&&d));
return 0;
}
=======


int a;

int b;

int c;

int d;

a=0; 

b=0;

c=0;

d=0;

if(i) {

if(j) {

a=1;

} else {

b=1;

}

} else {

if(z) {

c=1;

} else {

d=1;

}

}

assert(0);
assert(!(i&&j)||(a&&!b&&!c&&!d));

assert(!(i&&!j)||(!a&&b&&!c&&!d));

assert(!(!i&&z)||(!a&&!b&&c&&!d));

assert(!(!i&&!z)||(!a&&!b&&!c&&d));

return 0;

}
>>>>>>> branch 'master' of https://github.com/w460461339/softwareReliability.git
