#include <stdint.h>

struct Point {
    int32_t x;
    int32_t y;
};

void swap(struct Point *p)
//@ requires p->x |-> ?_pre_p_x &*& p->y |-> ?_pre_p_y;
//@ ensures p->x |-> ?_post_p_x &*& p->y |-> ?_post_p_y &*& _post_p_x == _pre_p_y &*& _post_p_y == _pre_p_x;
{
    int32_t temp = p->x;
    p->x = p->y;
    p->y = temp;
}

int32_t mangle(struct Point *p)
//@ requires p->x |-> ?_pre_p_x &*& p->y |-> ?_pre_p_y;
//@ ensures p->x |-> ?_post_p_x &*& p->y |-> ?_post_p_y &*& _post_p_x == _pre_p_y + _pre_p_x &*& _post_p_y == _pre_p_y - _pre_p_x &*& result == _post_p_x * _post_p_y;
{
    int32_t x = p->x, y = p ->y;
    p->x = y + x;
    p->y = y - x;
    return p->x * p->y;
}

int32_t squared_magnitude(struct Point *p)
//@ requires [?_frac_0]p->x |-> ?_pre_p_x &*& [?_frac_1]p->y |-> ?_pre_p_y;
//@ ensures [_frac_0]p->x |-> ?_post_p_x &*& [_frac_1]p->y |-> ?_post_p_y &*& result == _post_p_x * _post_p_x + _post_p_y * _post_p_y;
{
    return p->x * p->x + p->y * p->y;
}